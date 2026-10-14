/*
 * Single-file oscilloscope for STM32F401RCT6 + 320x240 SPI ILI9341.
 * STM32CubeIDE: MCU STM32F401RCTx, preprocessor symbol STM32F401xC.
 * Replace Core/Src/main.c; keep CubeIDE's generated CMSIS/startup/linker files.
 * Direct register control only: no HAL, LL, Arduino, Adafruit, stdio, or libc.
 * The device header supplies register addresses/types and CPU instructions.
 * Text formatting and integer division are implemented in this same file.
 *
 * Wiring (3.3 V GPIO):
 *   TFT SCK=PA5, MOSI=PA7, CS=PB1, DC=PB10, RESET=PB11.
 *   Buttons: HOLD=PB12, UP=PB13, DOWN=PB14, SET=PB15; other ends to GND.
 *   ADC: PA0. Input -> R2 -> PA0; PA0 -> R1 -> GND. PA2 is UNUSED.
 *   R2=9100 ohms, R1=1000 ohms: attenuation 10.1:1, nominal FS=33.33 V.
 *   Use 0..30 V positive input for headroom. Keep PA0 within 0..VDDA.
 *   Upper clamp: anode PA0, cathode 3.3 V. Lower: anode GND, cathode PA0.
 *   Clamps are supplementary protection, not a guaranteed overvoltage barrier.
 *   For this ground-referenced divider, close the AC/DC switch (bypass C1).
 *   Opening C1 does NOT make negative input voltages measurable: AC needs bias.
 *
 * CPU=64 MHz from internal HSI PLL; APB1=32 MHz, APB2=64 MHz.
 * ADC1 clock=32 MHz, sample time=15 cycles, 12-bit conversion=12 cycles.
 * TIM2 update/TRGO sets the sample interval; DMA2 Stream0 Channel0 stores ADC.
 * Maximum configured sampling=1 MS/s. Use about 100 kHz or less for shape;
 * 500 kHz at this rate cannot be represented accurately.
 * SPI1=8 MHz, within the ILI9341's documented serial write timing.
 * HSI tolerance affects timing/frequency; calibrate against a known reference.
 *
 * Controls: SET cycles TIME / VOLTS / TRIG. UP/DOWN adjust the selected item.
 * HOLD freezes/resumes the last trace. TRIG is % of the captured signal span.
 * Vertical zoom only changes drawing; the physical divider always stays fixed.
 * Measurements are VMIN/VMAX/VPP and an estimated rising-edge frequency.
 * The trigger aligns a captured block in software; AUTO means no crossing found.
 * After a capture error, HOLD retries. No simulated data or software fallback.
 *
 * Calibration: enter measured VDDA and resistor values below. A known DC input
 * can additionally calibrate gain/offset. ADC resolution is not absolute accuracy.
 */
#include "stm32f401xc.h" /* Register definitions, not a hardware driver library. */

#if !defined(STM32F401xC)
#error "Select STM32F401RCTx / define STM32F401xC in STM32CubeIDE."
#endif

/* These values MUST match the physical, ground-referenced input divider. */
#define R1_OHMS           1000U
#define R2_OHMS           9100U
#define VDDA_MV           3300U
#define CAL_GAIN_PPM      1000000L /* 1000000 = unity; known / displayed voltage. */
#define CAL_OFFSET_MV     0L       /* Input-referred correction, normally zero. */
#define SYSCLK_HZ         64000000U
#define ADC_COUNT         1024U
#define LCD_W             320U
#define PLOT_TOP          32U
#define PLOT_H            192U
#define LCD_CS            (1U << 1)
#define LCD_DC            (1U << 10)
#define LCD_RST           (1U << 0)
#define BLACK             0x0000U
#define WHITE             0xFFFFU
#define GRID              0x2104U
#define RED               0xF800U
#define YELLOW            0xFFE0U
#define GREEN             0x07E0U
#define DMA_CLEAR0        (DMA_LIFCR_CFEIF0 | DMA_LIFCR_CDMEIF0 | \
                           DMA_LIFCR_CTEIF0 | DMA_LIFCR_CHTIF0 | DMA_LIFCR_CTCIF0)
#define DMA_ERROR0        (DMA_LISR_FEIF0 | DMA_LISR_DMEIF0 | DMA_LISR_TEIF0)

static volatile uint16_t samples[ADC_COUNT];
static uint16_t trace[LCD_W], trace_y[LCD_W];
static const uint32_t time_us[] = {2,5,10,20,50,100,200,500,1000,2000,5000,10000};
static const uint32_t volts_mv[] = {100,200,500,1000,2000,5000,10000};
static uint8_t time_index=5, volt_index=6, selected=0, hold=0, have_trace=0;
static uint8_t active=0, fault=0, triggered=0, high_clip=0, trigger_percent=50;
static uint32_t period_ticks, capture_started, capture_timeout;
static uint32_t last_period=64, frequency_hz=0;
static int32_t vmin_mv=0, vmax_mv=0, vpp_mv=0;
static uint8_t key_stable=0, key_candidate=0, key_events=0;
static uint32_t key_changed=0;

void Error_Handler(void);

/* Avoid external 64-bit division helpers; Cortex-M4 handles 32-bit division. */
static uint64_t divide_u64(uint64_t numerator, uint64_t denominator)
{
    uint64_t quotient=0, bit=1;
    if (denominator==0U) Error_Handler();
    while (denominator<=numerator && (denominator & (1ULL<<63))==0U) {
        denominator<<=1; bit<<=1;
    }
    while (bit!=0U) {
        if (numerator>=denominator) { numerator-=denominator; quotient|=bit; }
        denominator>>=1; bit>>=1;
    }
    return quotient;
}

static void clock_init(void)
{
    uint32_t budget=2000000U;
    SysTick->CTRL=0; /* Timing uses TIM5; no custom SysTick_Handler is required. */
    RCC->CR |= RCC_CR_HSION;
    while (!(RCC->CR & RCC_CR_HSIRDY)) if (--budget==0U) Error_Handler();
    RCC->CFGR &= ~RCC_CFGR_SW;
    budget=2000000U;
    while ((RCC->CFGR & RCC_CFGR_SWS)!=0U) if (--budget==0U) Error_Handler();
    RCC->CR &= ~RCC_CR_PLLON;
    budget=2000000U;
    while (RCC->CR & RCC_CR_PLLRDY) if (--budget==0U) Error_Handler();
    RCC->APB1ENR |= RCC_APB1ENR_PWREN;
    (void)RCC->APB1ENR;
    PWR->CR = (PWR->CR & ~PWR_CR_VOS) | PWR_CR_VOS_1; /* Scale 2. */
    FLASH->ACR = FLASH_ACR_ICEN | FLASH_ACR_DCEN | FLASH_ACR_PRFTEN |
                 FLASH_ACR_LATENCY_2WS;
    /* HSI 16 MHz / M=16 * N=256 / P=4 = 64 MHz. USB is not used. */
    RCC->PLLCFGR = 16U | (256U<<6) | (1U<<16) | (6U<<24);
    RCC->CFGR = (RCC->CFGR & ~(RCC_CFGR_HPRE | RCC_CFGR_PPRE1 |
                              RCC_CFGR_PPRE2)) | RCC_CFGR_PPRE1_DIV2;
    RCC->CR |= RCC_CR_PLLON;
    budget=2000000U;
    while (!(RCC->CR & RCC_CR_PLLRDY)) if (--budget==0U) Error_Handler();
    RCC->CFGR = (RCC->CFGR & ~RCC_CFGR_SW) | RCC_CFGR_SW_PLL;
    budget=2000000U;
    while ((RCC->CFGR & RCC_CFGR_SWS)!=RCC_CFGR_SWS_PLL)
        if (--budget==0U) Error_Handler();
    SystemCoreClock=SYSCLK_HZ;
}

static uint32_t micros_now(void) { return TIM5->CNT; }

static void delay_us(uint32_t us)
{
    uint32_t start=micros_now();
    while ((uint32_t)(micros_now()-start)<us) { __NOP(); }
}

static void timebase_init(void)
{
    RCC->APB1ENR |= RCC_APB1ENR_TIM5EN;
    (void)RCC->APB1ENR;
    TIM5->CR1=0;
    TIM5->PSC=63; /* APB1 timers run at 64 MHz: divide by 64 -> 1 MHz. */
    TIM5->ARR=0xFFFFFFFFU;
    TIM5->EGR=TIM_EGR_UG;
    TIM5->SR=0;
    TIM5->CNT=0;
    TIM5->CR1=TIM_CR1_CEN;
}

/* PB12..15 have internal pull-ups; one debounced press generates one event. */
static void keys_scan(void)
{
    uint8_t now=(uint8_t)((~GPIOB->IDR>>12)&15U);
    if (now!=key_candidate) { key_candidate=now; key_changed=micros_now(); }
    if (now!=key_stable && (uint32_t)(micros_now()-key_changed)>=20000U) {
        key_events |= (uint8_t)(now & (uint8_t)~key_stable);
        key_stable=now;
    }
}

static void pins_init(void)
{
    const uint32_t outputs=LCD_CS|LCD_DC|LCD_RST;
    RCC->AHB1ENR |= RCC_AHB1ENR_GPIOAEN | RCC_AHB1ENR_GPIOBEN | RCC_AHB1ENR_DMA2EN;
    RCC->APB2ENR |= RCC_APB2ENR_SPI1EN | RCC_APB2ENR_ADC1EN;
    RCC->APB1ENR |= RCC_APB1ENR_TIM2EN;
    (void)RCC->AHB1ENR;
    (void)RCC->APB2ENR;
    (void)RCC->APB1ENR;
    GPIOA->MODER = (GPIOA->MODER & ~((3U<<0)|(3U<<10)|(3U<<14))) |
                   (3U<<0)|(2U<<10)|(2U<<14); // PA0 la chan analog; PA5/7 la chan alternate.
    GPIOA->PUPDR &= ~((3U<<0)|(3U<<10)|(3U<<14));
    GPIOA->OTYPER &= ~((1U<<5)|(1U<<7));
    GPIOA->OSPEEDR |= (3U<<10)|(3U<<14);
    GPIOA->AFR[0] = (GPIOA->AFR[0] & ~((15U<<20)|(15U<<28))) |
                    (5U<<20)|(5U<<28); //AF5 = SPI1.
    GPIOB->BSRR=outputs;
    for (uint32_t pin=0; pin<16U; ++pin) {
        if ((outputs & (1U<<pin))!=0U) {
            GPIOB->MODER=(GPIOB->MODER & ~(3U<<(2U*pin))) | (1U<<(2U*pin));
            GPIOB->PUPDR &= ~(3U<<(2U*pin));
            GPIOB->OSPEEDR |= 3U<<(2U*pin);
        }
    }
    GPIOB->OTYPER &= ~outputs;
    GPIOB->MODER &= ~0xFF000000U;
    GPIOB->PUPDR = (GPIOB->PUPDR & ~0xFF000000U) | 0x55000000U;
    SPI1->CR1=0;
    SPI1->CR2=0;
    SPI1->CR1=SPI_CR1_MSTR | (2U<<3) | SPI_CR1_SSM | SPI_CR1_SSI |
              SPI_CR1_BIDIMODE | SPI_CR1_BIDIOE | SPI_CR1_SPE; /* Mode 0, 8 MHz. */
    ADC->CCR=0; /* PCLK2 / 2 = 32 MHz; independent ADC1. */
    ADC1->CR1=0; /* 12 bits, one regular channel, no interrupts. */
    ADC1->CR2=0;
    ADC1->SMPR1=0;
    ADC1->SMPR2=1U; /* ADC_IN0 sample time: 15 ADC clocks. */
    ADC1->SQR1=0;
    ADC1->SQR2=0;
    ADC1->SQR3=0; /* ADC_IN0 = PA0. */
}

static void spi_byte(uint8_t value)
{
    while (!(SPI1->SR & SPI_SR_TXE)) { }
    *(volatile uint8_t *)&SPI1->DR=value;
}

static void spi_idle(void) { while (SPI1->SR & SPI_SR_BSY) { } }

static void lcd_command(uint8_t cmd, const uint8_t *data, uint32_t count)
{
    GPIOB->BSRR=(LCD_CS|LCD_DC)<<16;
    spi_byte(cmd);
    spi_idle();
    GPIOB->BSRR=LCD_DC;
    while (count--!=0U) spi_byte(*data++);
    spi_idle();
    GPIOB->BSRR=LCD_CS;
}

/* Opens a RAM-write transaction; caller streams RGB565 high byte first. */
static void lcd_window(uint16_t x0, uint16_t y0, uint16_t x1, uint16_t y1)
{
    uint8_t d[4]={(uint8_t)(x0>>8),(uint8_t)x0,(uint8_t)(x1>>8),(uint8_t)x1};
    lcd_command(0x2A,d,4);
    d[0]=(uint8_t)(y0>>8); d[1]=(uint8_t)y0;
    d[2]=(uint8_t)(y1>>8); d[3]=(uint8_t)y1;
    lcd_command(0x2B,d,4);
    GPIOB->BSRR=(LCD_CS|LCD_DC)<<16;
    spi_byte(0x2C);
    spi_idle();
    GPIOB->BSRR=LCD_DC;
}

static void lcd_close(void) { spi_idle(); GPIOB->BSRR=LCD_CS; }
static void pixel_color(uint16_t c) { spi_byte((uint8_t)(c>>8)); spi_byte((uint8_t)c); }

static void lcd_fill(uint16_t x, uint16_t y, uint16_t w, uint16_t h, uint16_t c)
{
    lcd_window(x,y,(uint16_t)(x+w-1U),(uint16_t)(y+h-1U));
    for (uint32_t n=(uint32_t)w*h; n!=0U; --n) pixel_color(c);
    lcd_close();
}

static void lcd_init(void)
{
    /* ILI9341 power, frame-rate, RGB565 and landscape configuration. */
    static const uint8_t init[]={
        0xEF,3,0x03,0x80,0x02, 0xCF,3,0x00,0xC1,0x30,
        0xED,4,0x64,0x03,0x12,0x81, 0xE8,3,0x85,0x00,0x78,
        0xCB,5,0x39,0x2C,0x00,0x34,0x02, 0xF7,1,0x20,
        0xEA,2,0x00,0x00, 0xC0,1,0x23, 0xC1,1,0x10,
        0xC5,2,0x3E,0x28, 0xC7,1,0x86, 0x36,1,0x28,
        0x3A,1,0x55, 0xB1,2,0x00,0x18, 0xB6,3,0x08,0x82,0x27,
        0xF2,1,0x00, 0x26,1,0x01
    };
    GPIOB->BSRR=LCD_CS|LCD_DC|LCD_RST;
    GPIOB->BSRR=LCD_RST<<16; delay_us(20000);
    GPIOB->BSRR=LCD_RST; delay_us(150000);
    lcd_command(0x01,0,0); delay_us(150000);
    for (uint32_t p=0; p<sizeof(init); ) {
        uint8_t cmd=init[p++], len=init[p++];
        lcd_command(cmd,&init[p],len); p+=len;
    }
    lcd_command(0x11,0,0); delay_us(120000);
    lcd_command(0x29,0,0); delay_us(20000);
    lcd_fill(0,0,320,240,BLACK);
}

/* Small uppercase 5x7 font, kept here to avoid a separate font/driver file. */
static const char glyph_names[]="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ .:-/%";
static const uint8_t glyphs[][5]={
 {0x3E,0x51,0x49,0x45,0x3E},{0,0x42,0x7F,0x40,0},{0x42,0x61,0x51,0x49,0x46},
 {0x21,0x41,0x45,0x4B,0x31},{0x18,0x14,0x12,0x7F,0x10},{0x27,0x45,0x45,0x45,0x39},
 {0x3C,0x4A,0x49,0x49,0x30},{1,0x71,9,5,3},{0x36,0x49,0x49,0x49,0x36},
 {6,0x49,0x49,0x29,0x1E},
 {0x7E,0x11,0x11,0x11,0x7E},{0x7F,0x49,0x49,0x49,0x36},{0x3E,0x41,0x41,0x41,0x22},
 {0x7F,0x41,0x41,0x22,0x1C},{0x7F,0x49,0x49,0x49,0x41},{0x7F,9,9,9,1},
 {0x3E,0x41,0x49,0x49,0x7A},{0x7F,8,8,8,0x7F},{0,0x41,0x7F,0x41,0},
 {0x20,0x40,0x41,0x3F,1},{0x7F,8,0x14,0x22,0x41},{0x7F,0x40,0x40,0x40,0x40},
 {0x7F,2,0x0C,2,0x7F},{0x7F,4,8,0x10,0x7F},{0x3E,0x41,0x41,0x41,0x3E},
 {0x7F,9,9,9,6},{0x3E,0x41,0x51,0x21,0x5E},{0x7F,9,0x19,0x29,0x46},
 {0x46,0x49,0x49,0x49,0x31},{1,1,0x7F,1,1},{0x3F,0x40,0x40,0x40,0x3F},
 {0x1F,0x20,0x40,0x20,0x1F},{0x3F,0x40,0x38,0x40,0x3F},{0x63,0x14,8,0x14,0x63},
 {7,8,0x70,8,7},{0x61,0x51,0x49,0x45,0x43},
 {0,0,0,0,0},{0,0x60,0x60,0,0},{0,0x36,0x36,0,0},{8,8,8,8,8},
 {0x20,0x10,8,4,2},{0x63,0x13,8,0x64,0x63}
};

static void lcd_text(uint16_t x, uint16_t y, const char *s, uint16_t color)
{
    while (*s!=0 && x+6U<=LCD_W) {
        uint32_t g=36; /* Unsupported character -> space. */
        for (uint32_t i=0; i<sizeof(glyph_names)-1U; ++i)
            if (glyph_names[i]==*s) { g=i; break; }
        lcd_window(x,y,(uint16_t)(x+5U),(uint16_t)(y+7U));
        for (uint32_t row=0; row<8U; ++row)
            for (uint32_t col=0; col<6U; ++col)
                pixel_color(col<5U && ((glyphs[g][col]>>row)&1U) ? color : BLACK);
        lcd_close(); x+=6U; ++s;
    }
}

static int32_t input_mv(uint16_t raw)
{
    uint64_t full=divide_u64((uint64_t)VDDA_MV*(R1_OHMS+R2_OHMS),R1_OHMS);
    uint64_t value=divide_u64((uint64_t)raw*full+2047U,4095U);
    return (int32_t)divide_u64(value*(uint64_t)CAL_GAIN_PPM,1000000U)+CAL_OFFSET_MV;
}

/* Bounded text append and decimal conversion; no printf/string library calls. */
static void text_append(char *out, uint32_t capacity, const char *text)
{
    uint32_t used=0;
    if (capacity==0U) return;
    while (used+1U<capacity && out[used]!=0) ++used;
    while (used+1U<capacity && *text!=0) out[used++]=*text++;
    out[used]=0;
}

static void text_uint(char *out, uint32_t capacity, uint32_t value)
{
    char digits[11];
    uint32_t count=0;
    do { digits[count++]=(char)('0'+value%10U); value/=10U; } while (value!=0U);
    for (uint32_t i=0; i<count/2U; ++i) {
        char c=digits[i]; digits[i]=digits[count-1U-i]; digits[count-1U-i]=c;
    }
    digits[count]=0;
    text_append(out,capacity,digits);
}

static void text_volts(char *out, uint32_t capacity, int32_t mv)
{
    uint32_t magnitude=mv<0 ? 0U-(uint32_t)mv : (uint32_t)mv;
    char fraction[4]={(char)('0'+magnitude/100U%10U),
                      (char)('0'+magnitude/10U%10U),(char)('0'+magnitude%10U),0};
    if (mv<0) text_append(out,capacity,"-");
    text_uint(out,capacity,magnitude/1000U);
    text_append(out,capacity,".");
    text_append(out,capacity,fraction);
}

static void capture_stop(void)
{
    TIM2->CR1=0; /* Stop trigger before stopping DMA. */
    ADC1->CR2=0;
    DMA2_Stream0->CR &= ~DMA_SxCR_EN;
    uint32_t start=micros_now();
    while (DMA2_Stream0->CR & DMA_SxCR_EN)
        if ((uint32_t)(micros_now()-start)>1000U) Error_Handler();
    DMA2->LIFCR=DMA_CLEAR0;
    (void)ADC1->DR;
    ADC1->SR=0;
    active=0;
    __DMB();
}

static void capture_start(void)
{
    /* >=1 us sampling interval. At slower sweeps there is one sample/pixel. */
    period_ticks=time_us[time_index]*2U;
    if (period_ticks<64U) period_ticks=64U;
    capture_stop();
    TIM2->CR2=0; /* Prevent EGR.UG from accidentally triggering a conversion. */
    TIM2->PSC=0;
    TIM2->ARR=period_ticks-1U;
    TIM2->CNT=0;
    TIM2->EGR=TIM_EGR_UG;
    TIM2->SR=0;
    TIM2->CR2=2U<<4; /* MMS=010: update -> TRGO. */
    DMA2_Stream0->CR=DMA_SxCR_MINC|DMA_SxCR_MSIZE_0|DMA_SxCR_PSIZE_0|DMA_SxCR_PL_1;
    DMA2_Stream0->FCR=0; /* Direct mode, single halfword transfers. */
    DMA2_Stream0->PAR=(uint32_t)(uintptr_t)&ADC1->DR;
    DMA2_Stream0->M0AR=(uint32_t)(uintptr_t)samples;
    DMA2_Stream0->NDTR=ADC_COUNT;
    DMA2->LIFCR=DMA_CLEAR0;
    DMA2_Stream0->CR |= DMA_SxCR_EN;
    ADC1->CR2=ADC_CR2_DMA|ADC_CR2_DDS|ADC_CR2_EOCS|ADC_CR2_ADON|
              (6U<<24)|ADC_CR2_EXTEN_0; /* EXTSEL=0110: TIM2 TRGO, rising. */
    delay_us(10); /* ADC power-up settling before first trigger. */
    capture_timeout=(uint32_t)(((uint64_t)ADC_COUNT*period_ticks+63U)>>6)+10000U;
    capture_started=micros_now();
    active=1;
    TIM2->CR1=TIM_CR1_CEN;
}

/* 0=busy, 1=complete, 2=DMA fault, 3=ADC overrun, 4=timeout. */
static uint8_t capture_poll(void)
{
    uint32_t flags=DMA2->LISR;
    uint8_t result=0;
    if (flags & DMA_ERROR0) result=2;
    else if (flags & DMA_LISR_TCIF0) result=1;
    else if (ADC1->SR & ADC_SR_OVR) result=3;
    else if ((uint32_t)(micros_now()-capture_started)>capture_timeout) result=4;
    if (result!=0U) capture_stop();
    return result;
}

static void analyze_capture(void)
{
    uint16_t lo=4095, hi=0;
    for (uint32_t i=0; i<ADC_COUNT; ++i) {
        uint16_t s=samples[i];
        if (s<lo) lo=s;
        if (s>hi) hi=s;
    }
    uint16_t level=(uint16_t)(lo+(uint32_t)(hi-lo)*trigger_percent/100U);
    uint32_t span_q16=(uint32_t)divide_u64((uint64_t)time_us[time_index]*10U*
                          SYSCLK_HZ*65536U,(uint64_t)period_ticks*1000000U);
    uint32_t span=(span_q16+65535U)>>16;
    uint32_t start=0;
    triggered=0;
    if ((uint32_t)(hi-lo)>=16U) {
        for (uint32_t i=1; i<ADC_COUNT-span-2U && i<ADC_COUNT/2U; ++i) {
            if (samples[i-1U]<level && samples[i]>=level) {
                start=i; triggered=1; break;
            }
        }
    }
    for (uint32_t x=0; x<LCD_W; ++x) {
        uint32_t pos=(uint32_t)divide_u64((uint64_t)x*span_q16,LCD_W-1U);
        uint32_t i=start+(pos>>16), frac=pos&65535U;
        /* Interpolation connects actual samples; it does not increase bandwidth. */
        trace[x]=(uint16_t)(((uint32_t)samples[i]*(65536U-frac)+
                             (uint32_t)samples[i+1U]*frac+32768U)>>16);
    }
    uint16_t visible_lo=4095, visible_hi=0;
    for (uint32_t i=start; i<=start+span; ++i) {
        uint16_t s=samples[i];
        if (s<visible_lo) visible_lo=s;
        if (s>visible_hi) visible_hi=s;
    }
    vmin_mv=input_mv(visible_lo); vmax_mv=input_mv(visible_hi);
    vpp_mv=vmax_mv-vmin_mv;
    high_clip=(uint8_t)(hi>=4090U);
    /* Schmitt-armed midpoint crossings; average all complete measured periods. */
    frequency_hz=0;
    if ((uint32_t)(hi-lo)>=20U) {
        uint16_t mid=(uint16_t)(lo+(hi-lo)/2U), hyst=(uint16_t)((hi-lo)/20U);
        if (hyst<4U) hyst=4U;
        uint8_t armed=0;
        uint32_t first=0, last=0, edges=0;
        for (uint32_t i=1; i<ADC_COUNT; ++i) {
            if (samples[i]<mid-hyst) armed=1;
            if (armed && samples[i-1U]<mid && samples[i]>=mid) {
                uint32_t crossing=(i-1U)*65536U+
                    (uint32_t)divide_u64((uint64_t)(mid-samples[i-1U])*65536U,
                                         samples[i]-samples[i-1U]);
                if (edges==0U) first=crossing;
                last=crossing; ++edges; armed=0;
            }
        }
        if (edges>=2U && last>first)
            frequency_hz=(uint32_t)divide_u64((uint64_t)SYSCLK_HZ*(edges-1U)*65536U,
                                            (uint64_t)period_ticks*(last-first));
    }
    last_period=period_ticks;
    have_trace=1;
}

static void draw_plot(void)
{
    int32_t full_height=(int32_t)(4U*volts_mv[volt_index]);
    for (uint32_t x=0; x<LCD_W; ++x) {
        int32_t mv=have_trace ? input_mv(trace[x]) : 0;
        uint32_t height=mv<=0 ? 0U :
            (uint32_t)divide_u64((uint64_t)(uint32_t)mv*(PLOT_H-1U),(uint32_t)full_height);
        if (height>PLOT_H-1U) height=PLOT_H-1U;
        trace_y[x]=(uint16_t)(PLOT_H-1U-height);
    }
    /* One streamed row at a time; no full-screen framebuffer is allocated. */
    for (uint32_t y=0; y<PLOT_H; ++y) {
        lcd_window(0,(uint16_t)(PLOT_TOP+y),319,(uint16_t)(PLOT_TOP+y));
        for (uint32_t x=0; x<LCD_W; ++x) {
            uint16_t c=(x%32U==0U || y%48U==0U || y==PLOT_H-1U) ? GRID : BLACK;
            if (have_trace) {
                uint16_t a=trace_y[x], b=trace_y[x==0U ? 0U : x-1U];
                uint16_t top=a<b ? a : b, bottom=a>b ? a : b;
                if (y>=top && y<=bottom) c=RED;
            }
            pixel_color(c);
        }
        lcd_close();
        keys_scan(); /* Do not lose button presses during a screen transfer. */
    }
}

static void draw_labels(void)
{
    const char *settings[]={"TIME","VOLTS","TRIG"};
    char line[64];
    lcd_fill(0,0,320,32,BLACK);
    lcd_fill(0,224,320,16,BLACK);
    line[0]=0;
    text_append(line,sizeof(line),"F401 SCOPE ");
    text_append(line,sizeof(line),fault ? "ERROR" : (hold ? "HOLD" : "RUN"));
    text_append(line,sizeof(line)," ");
    text_append(line,sizeof(line),settings[selected]);
    text_append(line,sizeof(line)," ");
    text_append(line,sizeof(line),triggered ? "TRIGGERED" : "AUTO");
    lcd_text(0,0,line,hold ? YELLOW : GREEN);
    uint32_t t=time_us[time_index];
    line[0]=0;
    text_append(line,sizeof(line),"T:");
    text_uint(line,sizeof(line),t>=1000U ? t/1000U : t);
    text_append(line,sizeof(line),t>=1000U ? "MS/DIV V:" : "US/DIV V:");
    text_volts(line,sizeof(line),(int32_t)volts_mv[volt_index]);
    text_append(line,sizeof(line),"V/DIV TR:");
    text_uint(line,sizeof(line),trigger_percent);
    text_append(line,sizeof(line),"%");
    lcd_text(0,10,line,WHITE);
    line[0]=0;
    text_append(line,sizeof(line),"MIN:"); text_volts(line,sizeof(line),vmin_mv);
    text_append(line,sizeof(line)," MAX:"); text_volts(line,sizeof(line),vmax_mv);
    text_append(line,sizeof(line)," PP:"); text_volts(line,sizeof(line),vpp_mv);
    text_append(line,sizeof(line),"V");
    lcd_text(0,20,line,WHITE);
    if (fault) {
        lcd_text(0,228,fault==2U ? "DMA ERROR - HOLD TO RETRY" :
                      (fault==3U ? "ADC OVERRUN - HOLD TO RETRY" :
                                   "ADC TIMEOUT - HOLD TO RETRY"),YELLOW);
    } else {
        uint32_t rate=SYSCLK_HZ/last_period;
        line[0]=0;
        text_append(line,sizeof(line),"FS:");
        if (rate>=1000U) {
            text_uint(line,sizeof(line),rate/1000U);
            text_append(line,sizeof(line),".");
            text_uint(line,sizeof(line),rate%1000U/100U);
            text_append(line,sizeof(line),"KSPS");
        } else { text_uint(line,sizeof(line),rate); text_append(line,sizeof(line),"SPS"); }
        text_append(line,sizeof(line)," F:");
        if (frequency_hz==0U) text_append(line,sizeof(line),"---");
        else { text_uint(line,sizeof(line),frequency_hz); text_append(line,sizeof(line),"HZ"); }
        const char *status=high_clip ? "HIGH CLIP" :
            (frequency_hz!=0U && frequency_hz>rate/10U ? "FEW SAMPLES" : "");
        text_append(line,sizeof(line)," "); text_append(line,sizeof(line),status);
        lcd_text(0,228,line,high_clip ? YELLOW : WHITE);
    }
    keys_scan();
}

static void apply_keys(uint8_t keys)
{
    if (active) capture_stop();
    if (keys&1U) {
        if (fault) { fault=0; hold=0; }
        else hold^=1U;
    }
    if (keys&8U) selected=(uint8_t)((selected+1U)%3U);
    int32_t step=(keys&2U ? 1 : 0)-(keys&4U ? 1 : 0);
    uint8_t redraw=0;
    if (step!=0) {
        if (selected==0U && !hold) {
            /* UP = faster sweep; DOWN = slower sweep. */
            int32_t i=(int32_t)time_index-step;
            if (i>=0 && i<(int32_t)(sizeof(time_us)/sizeof(time_us[0]))) time_index=(uint8_t)i;
        } else if (selected==1U) {
            /* UP = vertical magnification (smaller V/div). */
            int32_t i=(int32_t)volt_index-step;
            if (i>=0 && i<(int32_t)(sizeof(volts_mv)/sizeof(volts_mv[0]))) {
                volt_index=(uint8_t)i; redraw=1;
            }
        } else if (selected==2U && !hold) {
            int32_t p=(int32_t)trigger_percent+step*5;
            if (p>=5 && p<=95) trigger_percent=(uint8_t)p;
        }
    }
    if (redraw) draw_plot();
    draw_labels();
}

int main(void)
{
    clock_init();
    timebase_init();
    pins_init();
    lcd_init();
    draw_plot();
    draw_labels();
    for (;;) {
        keys_scan();
        if (key_events!=0U) {
            uint8_t keys=key_events;
            key_events=0;
            apply_keys(keys);
        }
        if (hold) continue;
        if (!active) capture_start();
        uint8_t result=capture_poll();
        if (result==1U) {
            analyze_capture();
            draw_plot();
            draw_labels();
        } else if (result>1U) {
            fault=result; hold=1;
            draw_labels();
        }
    }
}

void Error_Handler(void)
{
    __disable_irq();
    /* Clock/stream-disable failure: halt for inspection with ST-LINK debugger. */
    for (;;) { __NOP(); }
}
