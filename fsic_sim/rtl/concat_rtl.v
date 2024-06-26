
//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_in_wait_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module ccs_in_wait_v1 (idat, rdy, ivld, dat, irdy, vld);

  parameter integer rscid = 1;
  parameter integer width = 8;

  output [width-1:0] idat;
  output             rdy;
  output             ivld;
  input  [width-1:0] dat;
  input              irdy;
  input              vld;

  wire   [width-1:0] idat;
  wire               rdy;
  wire               ivld;

  localparam stallOff = 0; 
  wire                  stall_ctrl;
  assign stall_ctrl = stallOff;

  assign idat = dat;
  assign rdy = irdy && !stall_ctrl;
  assign ivld = vld && !stall_ctrl;

endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_out_wait_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module ccs_out_wait_v1 (dat, irdy, vld, idat, rdy, ivld);

  parameter integer rscid = 1;
  parameter integer width = 8;

  output [width-1:0] dat;
  output             irdy;
  output             vld;
  input  [width-1:0] idat;
  input              rdy;
  input              ivld;

  wire   [width-1:0] dat;
  wire               irdy;
  wire               vld;

  localparam stallOff = 0; 
  wire stall_ctrl;
  assign stall_ctrl = stallOff;

  assign dat = idat;
  assign irdy = rdy && !stall_ctrl;
  assign vld = ivld && !stall_ctrl;

endmodule



//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/mgc_io_sync_v2.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module mgc_io_sync_v2 (ld, lz);
    parameter valid = 0;

    input  ld;
    output lz;

    wire   lz;

    assign lz = ld;

endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_in_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module ccs_in_v1 (idat, dat);

  parameter integer rscid = 1;
  parameter integer width = 8;

  output [width-1:0] idat;
  input  [width-1:0] dat;

  wire   [width-1:0] idat;

  assign idat = dat;

endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_in_wait_coupled_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module ccs_in_wait_coupled_v1 (idat, rdy, ivld, dat, irdy, vld);

  parameter integer rscid = 1;
  parameter integer width = 8;

  output [width-1:0] idat;
  output             rdy;
  output             ivld;
  input  [width-1:0] dat;
  input              irdy;
  input              vld;

  wire   [width-1:0] idat;
  wire               rdy;
  wire               ivld;

  assign idat = dat;
  assign rdy = irdy;
  assign ivld = vld;

endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_genreg_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------

module ccs_genreg_v1 (clk, en, arst, srst, d, z);
    parameter integer width   = 1;
    parameter integer ph_clk  = 1;
    parameter integer ph_en   = 1;
    parameter integer ph_arst = 0;
    parameter integer ph_srst = 1;
    parameter         has_en  = 1'b1;

    input clk;
    input en;
    input arst;
    input srst;
    input      [width-1:0] d;
    output reg [width-1:0] z;

    //  Generate parameters
    //  ph_clk | ph_arst | has_en     Label:
    //    1        1          1       GEN_CLK1_ARST1_EN1
    //    1        1          0       GEN_CLK1_ARST1_EN0
    //    1        0          1       GEN_CLK1_ARST0_EN1
    //    1        0          0       GEN_CLK1_ARST0_EN0
    //    0        1          1       GEN_CLK0_ARST1_EN1
    //    0        1          0       GEN_CLK0_ARST1_EN0
    //    0        0          1       GEN_CLK0_ARST0_EN1
    //    0        0          0       GEN_CLK0_ARST0_EN0
    
    generate 
      // Pos edge clock, pos edge async reset, has enable
      if (ph_clk == 1 & ph_arst == 1 & has_en == 1)
      begin: GEN_CLK1_ARST1_EN1
        always @(posedge clk or posedge arst)
          if (arst == 1'b1)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else if (en == $unsigned(ph_en))
            z <= d;
      end  //GEN_CLK1_ARST1_EN1

      // Pos edge clock, pos edge async reset, no enable
      else if (ph_clk == 1 & ph_arst == 1 & has_en == 0)
      begin: GEN_CLK1_ARST1_EN0
        always @(posedge clk or posedge arst)
          if (arst == 1'b1)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else
            z <= d;
      end  //GEN_CLK1_ARST1_EN0

      // Pos edge clock, neg edge async reset, has enable
      else if (ph_clk == 1 & ph_arst == 0 & has_en == 1)
      begin: GEN_CLK1_ARST0_EN1
        always @(posedge clk or negedge arst)
          if (arst == 1'b0)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else if (en == $unsigned(ph_en))
            z <= d;
      end  //GEN_CLK1_ARST0_EN1

      // Pos edge clock, neg edge async reset, no enable
      else if (ph_clk == 1 & ph_arst == 0 & has_en == 0)
      begin: GEN_CLK1_ARST0_EN0
        always @(posedge clk or negedge arst)
          if (arst == 1'b0)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else
            z <= d;
      end  //GEN_CLK1_ARST0_EN0


      // Neg edge clock, pos edge async reset, has enable
      if (ph_clk == 0 & ph_arst == 1 & has_en == 1)
      begin: GEN_CLK0_ARST1_EN1
        always @(negedge clk or posedge arst)
          if (arst == 1'b1)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else if (en == $unsigned(ph_en))
            z <= d;
      end  //GEN_CLK0_ARST1_EN1

      // Neg edge clock, pos edge async reset, no enable
      else if (ph_clk == 0 & ph_arst == 1 & has_en == 0)
      begin: GEN_CLK0_ARST1_EN0
        always @(negedge clk or posedge arst)
          if (arst == 1'b1)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else
            z <= d;
      end  //GEN_CLK0_ARST1_EN0

      // Neg edge clock, neg edge async reset, has enable
      else if (ph_clk == 0 & ph_arst == 0 & has_en == 1)
      begin: GEN_CLK0_ARST0_EN1
        always @(negedge clk or negedge arst)
          if (arst == 1'b0)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else if (en == $unsigned(ph_en))
            z <= d;
      end  //GEN_CLK0_ARST0_EN1

      // Neg edge clock, neg edge async reset, no enable
      else if (ph_clk == 0 & ph_arst == 0 & has_en == 0)
      begin: GEN_CLK0_ARST0_EN0
        always @(negedge clk or negedge arst)
          if (arst == 1'b0)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else
            z <= d;
      end  //GEN_CLK0_ARST0_EN0
    endgenerate
endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_fifo_wait_core_v5.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------

/*
 *            _________________________________________________
 * WRITER    |                                                 |   READER
 *           |               ccs_fifo_wait_core                |
 *           |             _____________________               |
 *        --<|  din_rdy --<|  ---------------- <|--- dout_rdy <|---
 *           |             |       FIFO         |              |
 *        ---|> din_vld ---|> ----------------  |>-- dout_vld  |>--
 *        ---|>     din ---|> ----------------  |>-- dout      |>--
 *           |             |____________________|              |
 *           |_________________________________________________|
 *
 *    rdy    - can be considered as a notFULL signal
 *    vld    - can be considered as a notEMPTY signal
 *    is_idle - clk can be safely gated
 *
 * Change History:
 *    2019-01-24 - Add assertion to verify rdy signal behavior under reset.
 *                 Fix bug in that behavior.
 */

module ccs_fifo_wait_core_v5 (clk, en, arst, srst, din_vld, din_rdy, din, dout_vld, dout_rdy, dout, sd, is_idle);

    parameter integer rscid    = 0;     // resource ID
    parameter integer width    = 8;     // fifo width
    parameter integer sz_width = 8;     // size of port for elements in fifo
    parameter integer fifo_sz  = 8;     // fifo depth
    parameter integer ph_clk   = 1;     // clock polarity 1=rising edge, 0=falling edge
    parameter integer ph_en    = 1;     // clock enable polarity
    parameter integer ph_arst  = 1;     // async reset polarity
    parameter integer ph_srst  = 1;     // sync reset polarity
    parameter integer ph_log2  = 3;     // log2(fifo_sz)

    input                 clk;
    input                 en;
    input                 arst;
    input                 srst;
    input                 din_vld;    // writer has valid data
    output                din_rdy;    // fifo ready for data (not full)
    input  [width-1:0]    din;
    output                dout_vld;   // fifo has valid data (not empty)
    input                 dout_rdy;   // reader ready for data
    output [width-1:0]    dout;
    output [sz_width-1:0] sd;
    output                is_idle;

    localparam integer fifo_b  = width * fifo_sz;
    localparam integer fifo_mx = (fifo_sz > 0) ? (fifo_sz-1) : 0 ;
    localparam integer fifo_mx_over_8 = fifo_mx / 8 ;

    reg      [fifo_mx:0] stat_pre;
    wire     [fifo_mx:0] stat;
    reg      [( (fifo_b > 0) ? fifo_b : 1)-1:0] buff_pre;
    wire     [( (fifo_b > 0) ? fifo_b : 1)-1:0] buff;
    reg      [fifo_mx:0] en_l;
    reg      [fifo_mx_over_8:0] en_l_s;

    reg      [width-1:0] buff_nxt;

    reg                  stat_nxt;
    reg                  stat_behind;
    reg                  stat_ahead;
    reg                  stat_tail;
    reg                  en_l_var;

    integer              i;
    genvar               eni;

    wire [32:0]          size_t;
    reg  [31:0]          count;
    reg  [31:0]          count_t;
    reg  [32:0]          n_elem;
    wire                 din_rdy_drv;
    wire                 dout_vld_drv;
    wire                 din_vld_int;
    wire                 hs_init;
    wire                 active;
    wire                 is_idle_drv;

    // synopsys translate_off
    reg  [31:0]          peak;
    initial
    begin
      peak  = 32'b0;
    end
    // synopsys translate_on

    assign din_rdy = din_rdy_drv;
    assign dout_vld = dout_vld_drv;
    assign is_idle = is_idle_drv;

    generate
    if ( fifo_sz > 0 )
    begin: FIFO_REG
      assign din_vld_int = din_vld & hs_init;
      assign din_rdy_drv = (dout_rdy | (~stat[0])) & hs_init;
      assign dout_vld_drv = din_vld_int | stat[fifo_sz-1];

      assign active = (din_vld_int & din_rdy_drv) | (dout_rdy & dout_vld_drv);
      assign is_idle_drv = (~active) & hs_init;

      assign size_t = (count - {31'b0, (dout_rdy & stat[fifo_sz-1])}) + {31'b0, din_vld_int};
      assign sd = size_t[sz_width-1:0];

      assign dout = (stat[fifo_sz-1]) ? buff[fifo_b-1:width*(fifo_sz-1)] : din;

      always @(*)
      begin: FIFOPROC
        n_elem = 33'b0;
        for (i = fifo_sz-1; i >= 0; i = i - 1)
        begin
          stat_behind = (i != 0) ? stat[i-1] : 1'b0;
          stat_ahead  = (i != (fifo_sz-1)) ? stat[i+1] : 1'b1;

          // Determine if this buffer element will have data
          stat_nxt = stat_ahead &                       // valid element ahead of this one (or head)
                       (stat_behind                     // valid element behind this one
                         | (stat[i] & (~dout_rdy))      // valid element and output not ready (in use and not shifted)
                         | (stat[i] & din_vld_int)      // valid element and input has data
                         | (din_vld_int & (~dout_rdy))  // input has data and output not ready
                       );
          stat_pre[i] = stat_nxt;

          // First empty elem when not shifting or last valid elem after shifting (assumes stat_behind == 0)
          stat_tail = stat_ahead & (((~stat[i]) & (~dout_rdy)) | (stat[i] & dout_rdy));

          if (dout_rdy & stat_behind)
          begin
            // shift valid element
            buff_nxt[0+:width] = buff[width*(i-1)+:width];
            en_l_var = 1'b1;
          end
          else if (din_vld_int & stat_tail)
          begin
            // update tail with input data
            buff_nxt = din;
            en_l_var = 1'b1;
          end
          else
          begin
            // no-op, disable register
            buff_nxt = din; // Don't care input to disabled flop
            en_l_var = 1'b0;
          end
          buff_pre[width*i+:width] = buff_nxt[0+:width];

          if (ph_en != 0)
            en_l[i] = en & en_l_var;
          else
            en_l[i] = en | ~en_l_var;

          if ((stat_ahead == 1'b1) & (stat[i] == 1'b0))
            //found tail, update the number of elements for count
            n_elem = ($unsigned(fifo_sz) - 1) - $unsigned(i);
        end //for loop

        // Enable for stat registers (partitioned into banks of eight)
        // Take care of the head first
        if (ph_en != 0)
          en_l_s[(((fifo_sz > 0) ? fifo_sz : 1)-1)/8] = en & active;
        else
          en_l_s[(((fifo_sz > 0) ? fifo_sz : 1)-1)/8] = en | ~active;

        // Now every eight
        for (i = fifo_sz-1; i >= 7; i = i - 1)
        begin
          if (($unsigned(i) % 32'd8) == 0)
          begin
            if (ph_en != 0)
              en_l_s[(i/8)-1] = en & (stat[i]) & (active);
            else
              en_l_s[(i/8)-1] = (en) | (~stat[i]) | (~active);
          end
        end

        // Update count and peak
        if ( stat[fifo_sz-1] == 1'b0 )
          count_t = 32'b0;
        else if ( stat[0] == 1'b1 )
          count_t = fifo_sz;
        else
          count_t = n_elem[31:0];
        count = count_t;
        // synopsys translate_off
        peak = (peak < count) ? count : peak;
        // synopsys translate_on
      end //FIFOPROC

      // Handshake valid after reset
      ccs_genreg_v1
      #(
        .width   (1),
        .ph_clk  (ph_clk),
        .ph_en   (1),
        .ph_arst (ph_arst),
        .ph_srst (ph_srst),
        .has_en  (1'b0)
      )
      HS_INIT_REG
      (
        .clk     (clk),
        .en      (1'b1),
        .arst    (arst),
        .srst    (srst),
        .d       (1'b1),
        .z       (hs_init)
      );

      // Buffer and status registers
      for (eni = fifo_sz-1; eni >= 0; eni = eni - 1)
      begin: GEN_REGS
        ccs_genreg_v1
        #(
          .width   (1),
          .ph_clk  (ph_clk),
          .ph_en   (ph_en),
          .ph_arst (ph_arst),
          .ph_srst (ph_srst),
          .has_en  (1'b1)
        )
        STATREG
        (
          .clk     (clk),
          .en      (en_l_s[eni/8]),
          .arst    (arst),
          .srst    (srst),
          .d       (stat_pre[eni]),
          .z       (stat[eni])
        );

        ccs_genreg_v1
        #(
          .width   (width),
          .ph_clk  (ph_clk),
          .ph_en   (ph_en),
          .ph_arst (ph_arst),
          .ph_srst (ph_srst),
          .has_en  (1'b1)
        )
        BUFREG
        (
          .clk     (clk),
          .en      (en_l[eni]),
          .arst    (arst),
          .srst    (srst),
          .d       (buff_pre[width*eni+:width]),
          .z       (buff[width*eni+:width])
        );
      end

    end
    else
    begin: FEED_THRU
      assign din_rdy_drv  = dout_rdy;
      assign dout_vld_drv = din_vld;
      assign dout     = din;
      // non-blocking is not II=1 when fifo_sz=0
      assign sd = {{(sz_width-1){1'b0}}, (din_vld & ~dout_rdy)};
      assign is_idle_drv = ~(din_vld & dout_rdy);
    end
    endgenerate

`ifdef RDY_ASRT
    generate
    if (ph_clk==1)
    begin: POS_CLK_ASSERT

       property rdyAsrt ;
         @(posedge clk) (srst==ph_srst) |=> (din_rdy==0);
       endproperty
       a1Pos: assert property(rdyAsrt);

       property rdyAsrtASync ;
         @(posedge clk) (arst==ph_arst) |-> (din_rdy==0);
       endproperty
       a2Pos: assert property(rdyAsrtASync);

    end else if (ph_clk==0)
    begin: NEG_CLK_ASSERT

       property rdyAsrt ;
         @(negedge clk) ((srst==ph_srst) || (arst==ph_arst)) |=> (din_rdy==0);
       endproperty
       a1Neg: assert property(rdyAsrt);

       property rdyAsrtASync ;
         @(negedge clk) (arst==ph_arst) |-> (din_rdy==0);
       endproperty
       a2Neg: assert property(rdyAsrtASync);

    end
    endgenerate
`endif

endmodule

//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_pipe_v6.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------
/*
 *
 *            _______________________________________________
 * WRITER    |                                              |          READER
 *           |                 ccs_pipe                     |
 *           |            ______________________            |
 *        --<| din_rdy --<|  ---------------- <|---dout_rdy<|---
 *           |            |       FIFO         |            |
 *        ---|>din_vld ---|> ----------------  |>--dout_vld |>--
 *        ---|>din -------|> ----------------  |> -----dout |>--
 *           |            |____________________|            |
 *           |______________________________________________|
 *
 *    din_rdy     - can be considered as a notFULL signal
 *    dout_vld    - can be considered as a notEMPTY signal
 *    write_stall - an internal debug signal formed from din_vld & !din_rdy
 *    read_stall  - an internal debug signal formed from dout_rdy & !dout_vld
 *    is_idle     - indicates the clock can be safely gated
 *    stall_ctrl  - Stall the pipe(fifo).  Used by STALL_FLAG_SV directive
 */

module ccs_pipe_v6 (clk, en, arst, srst, din_rdy, din_vld, din, dout_rdy, dout_vld, dout, 
                    sz, sz_req, is_idle);

    parameter integer rscid    = 0; // resource ID
    parameter integer width    = 8; // fifo width
    parameter integer sz_width = 8; // width of size of elements in fifo
    parameter integer fifo_sz  = 8; // fifo depth
    parameter integer log2_sz  = 3; // log2(fifo_sz)
    parameter integer ph_clk   = 1; // clock polarity 1=rising edge, 0=falling edge
    parameter integer ph_en    = 1; // clock enable polarity
    parameter integer ph_arst  = 1; // async reset polarity
    parameter integer ph_srst  = 1; // sync reset polarity

    // clock 
    input              clk;
    input              en;
    input              arst;
    input              srst;

    // writer
    output             din_rdy;
    input              din_vld;
    input  [width-1:0] din;

    // reader
    input              dout_rdy;
    output             dout_vld;
    output [width-1:0] dout;

    // size
    output [sz_width-1:0] sz;
    input                 sz_req;
    output                is_idle;

    localparam stallOff = 0; 
    wire                  stall_ctrl;
    assign stall_ctrl = stallOff;
   
    // synopsys translate_off
    wire   write_stall;
    wire   read_stall;
    assign write_stall = (din_vld & !din_rdy) | stall_ctrl;
    assign read_stall  = (dout_rdy & !dout_vld) | stall_ctrl;
    // synopsys translate_on

    wire    tmp_din_rdy;
    assign  din_rdy = tmp_din_rdy & !stall_ctrl;
    wire    tmp_dout_vld;
    assign  dout_vld = tmp_dout_vld & !stall_ctrl;
   
    ccs_fifo_wait_core_v5
    #(
        .rscid    (rscid),
        .width    (width),
        .sz_width (sz_width),
        .fifo_sz  (fifo_sz),
        .ph_clk   (ph_clk),
        .ph_en    (ph_en),
        .ph_arst  (ph_arst),
        .ph_srst  (ph_srst),
        .ph_log2  (log2_sz)
    )
    FIFO
    (
        .clk      (clk),
        .en       (en),
        .arst     (arst),
        .srst     (srst),
        .din_vld  (din_vld & !stall_ctrl),
        .din_rdy  (tmp_din_rdy),
        .din      (din),
        .dout_vld (tmp_dout_vld),
        .dout_rdy (dout_rdy & !stall_ctrl),
        .dout     (dout),
        .sd       (sz),
        .is_idle  (is_idle)
    );

endmodule


//------> ./rtl.v 
// ----------------------------------------------------------------------
//  HLS HDL:        Verilog Netlister
//  HLS Version:    2024.1/1091966 Production Release
//  HLS Date:       Wed Feb 14 09:07:18 PST 2024
// 
//  Generated by:   m111061605@ws33
//  Generated date: Sun Jun 16 20:56:52 2024
// ----------------------------------------------------------------------

// 
// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_7_16_10_648_648_16_5_gen
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_7_16_10_648_648_16_5_gen
    (
  en, q, we, d, adr, adr_d, d_d, en_d, we_d, q_d, port_0_rw_ram_ir_internal_RMASK_B_d,
      port_0_rw_ram_ir_internal_WMASK_B_d
);
  output en;
  input [15:0] q;
  output we;
  output [15:0] d;
  output [9:0] adr;
  input [9:0] adr_d;
  input [15:0] d_d;
  input en_d;
  input we_d;
  output [15:0] q_d;
  input port_0_rw_ram_ir_internal_RMASK_B_d;
  input port_0_rw_ram_ir_internal_WMASK_B_d;



  // Interconnect Declarations for Component Instantiations 
  assign en = (en_d);
  assign q_d = q;
  assign we = (port_0_rw_ram_ir_internal_WMASK_B_d);
  assign d = (d_d);
  assign adr = (adr_d);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_6_16_10_648_648_16_5_gen
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_6_16_10_648_648_16_5_gen
    (
  en, q, we, d, adr, adr_d, d_d, en_d, we_d, q_d, port_0_rw_ram_ir_internal_RMASK_B_d,
      port_0_rw_ram_ir_internal_WMASK_B_d
);
  output en;
  input [15:0] q;
  output we;
  output [15:0] d;
  output [9:0] adr;
  input [9:0] adr_d;
  input [15:0] d_d;
  input en_d;
  input we_d;
  output [15:0] q_d;
  input port_0_rw_ram_ir_internal_RMASK_B_d;
  input port_0_rw_ram_ir_internal_WMASK_B_d;



  // Interconnect Declarations for Component Instantiations 
  assign en = (en_d);
  assign q_d = q;
  assign we = (port_0_rw_ram_ir_internal_WMASK_B_d);
  assign d = (d_d);
  assign adr = (adr_d);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_run_fsm
//  FSM Module
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_run_fsm (
  clk, rst, arst_n, run_wen, fsm_output, VCOL_C_0_tr0, VROW_C_0_tr0
);
  input clk;
  input rst;
  input arst_n;
  input run_wen;
  output [3:0] fsm_output;
  reg [3:0] fsm_output;
  input VCOL_C_0_tr0;
  input VROW_C_0_tr0;


  // FSM State Type Declaration for EdgeDetect_IP_Denoise_IP_run_run_fsm_1
  parameter
    main_C_0 = 2'd0,
    VCOL_C_0 = 2'd1,
    VROW_C_0 = 2'd2,
    main_C_1 = 2'd3;

  reg [1:0] state_var;
  reg [1:0] state_var_NS;


  // Interconnect Declarations for Component Instantiations 
  always @(*)
  begin : EdgeDetect_IP_Denoise_IP_run_run_fsm_1
    case (state_var)
      VCOL_C_0 : begin
        fsm_output = 4'b0010;
        if ( VCOL_C_0_tr0 ) begin
          state_var_NS = VROW_C_0;
        end
        else begin
          state_var_NS = VCOL_C_0;
        end
      end
      VROW_C_0 : begin
        fsm_output = 4'b0100;
        if ( VROW_C_0_tr0 ) begin
          state_var_NS = main_C_1;
        end
        else begin
          state_var_NS = VCOL_C_0;
        end
      end
      main_C_1 : begin
        fsm_output = 4'b1000;
        state_var_NS = main_C_0;
      end
      // main_C_0
      default : begin
        fsm_output = 4'b0001;
        state_var_NS = VCOL_C_0;
      end
    endcase
  end

  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      state_var <= main_C_0;
    end
    else if ( rst ) begin
      state_var <= main_C_0;
    end
    else if ( run_wen ) begin
      state_var <= state_var_NS;
    end
  end

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_staller
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_staller (
  clk, rst, arst_n, run_wen, run_wten, dat_in_rsci_wen_comp, dat_out_rsci_wen_comp
);
  input clk;
  input rst;
  input arst_n;
  output run_wen;
  output run_wten;
  reg run_wten;
  input dat_in_rsci_wen_comp;
  input dat_out_rsci_wen_comp;



  // Interconnect Declarations for Component Instantiations 
  assign run_wen = dat_in_rsci_wen_comp & dat_out_rsci_wen_comp;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      run_wten <= 1'b0;
    end
    else if ( rst ) begin
      run_wten <= 1'b0;
    end
    else begin
      run_wten <= ~ run_wen;
    end
  end
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_ctrl_signal_triosy_obj_ctrl_signal_triosy_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_ctrl_signal_triosy_obj_ctrl_signal_triosy_wait_ctrl
    (
  run_wten, ctrl_signal_triosy_obj_iswt0, ctrl_signal_triosy_obj_biwt
);
  input run_wten;
  input ctrl_signal_triosy_obj_iswt0;
  output ctrl_signal_triosy_obj_biwt;



  // Interconnect Declarations for Component Instantiations 
  assign ctrl_signal_triosy_obj_biwt = (~ run_wten) & ctrl_signal_triosy_obj_iswt0;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_wait_dp (
  line_buf0_rsci_en_d, line_buf1_rsci_en_d, run_wen, line_buf0_rsci_cgo, line_buf0_rsci_cgo_ir_unreg,
      line_buf1_rsci_cgo, line_buf1_rsci_cgo_ir_unreg
);
  output line_buf0_rsci_en_d;
  output line_buf1_rsci_en_d;
  input run_wen;
  input line_buf0_rsci_cgo;
  input line_buf0_rsci_cgo_ir_unreg;
  input line_buf1_rsci_cgo;
  input line_buf1_rsci_cgo_ir_unreg;



  // Interconnect Declarations for Component Instantiations 
  assign line_buf0_rsci_en_d = run_wen & (line_buf0_rsci_cgo | line_buf0_rsci_cgo_ir_unreg);
  assign line_buf1_rsci_en_d = run_wen & (line_buf1_rsci_cgo | line_buf1_rsci_cgo_ir_unreg);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_dat_out_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_dat_out_wait_dp (
  clk, rst, arst_n, dat_out_rsci_oswt, dat_out_rsci_wen_comp, dat_out_rsci_biwt,
      dat_out_rsci_bdwt, dat_out_rsci_bcwt
);
  input clk;
  input rst;
  input arst_n;
  input dat_out_rsci_oswt;
  output dat_out_rsci_wen_comp;
  input dat_out_rsci_biwt;
  input dat_out_rsci_bdwt;
  output dat_out_rsci_bcwt;
  reg dat_out_rsci_bcwt;



  // Interconnect Declarations for Component Instantiations 
  assign dat_out_rsci_wen_comp = (~ dat_out_rsci_oswt) | dat_out_rsci_biwt | dat_out_rsci_bcwt;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dat_out_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      dat_out_rsci_bcwt <= 1'b0;
    end
    else begin
      dat_out_rsci_bcwt <= ~((~(dat_out_rsci_bcwt | dat_out_rsci_biwt)) | dat_out_rsci_bdwt);
    end
  end
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_dat_out_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_dat_out_wait_ctrl (
  run_wen, dat_out_rsci_oswt, dat_out_rsci_biwt, dat_out_rsci_bdwt, dat_out_rsci_bcwt,
      dat_out_rsci_irdy, dat_out_rsci_ivld_run_sct
);
  input run_wen;
  input dat_out_rsci_oswt;
  output dat_out_rsci_biwt;
  output dat_out_rsci_bdwt;
  input dat_out_rsci_bcwt;
  input dat_out_rsci_irdy;
  output dat_out_rsci_ivld_run_sct;


  // Interconnect Declarations
  wire dat_out_rsci_ogwt;


  // Interconnect Declarations for Component Instantiations 
  assign dat_out_rsci_bdwt = dat_out_rsci_oswt & run_wen;
  assign dat_out_rsci_biwt = dat_out_rsci_ogwt & dat_out_rsci_irdy;
  assign dat_out_rsci_ogwt = dat_out_rsci_oswt & (~ dat_out_rsci_bcwt);
  assign dat_out_rsci_ivld_run_sct = dat_out_rsci_ogwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_dat_in_rsci_dat_in_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_dat_in_rsci_dat_in_wait_ctrl (
  run_wen, dat_in_rsci_iswt0, dat_in_rsci_irdy_run_sct
);
  input run_wen;
  input dat_in_rsci_iswt0;
  output dat_in_rsci_irdy_run_sct;



  // Interconnect Declarations for Component Instantiations 
  assign dat_in_rsci_irdy_run_sct = dat_in_rsci_iswt0 & run_wen;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_17_16_10_648_648_16_5_gen
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_17_16_10_648_648_16_5_gen
    (
  en, q, we, d, adr, adr_d, d_d, en_d, we_d, q_d, port_0_rw_ram_ir_internal_RMASK_B_d,
      port_0_rw_ram_ir_internal_WMASK_B_d
);
  output en;
  input [15:0] q;
  output we;
  output [15:0] d;
  output [9:0] adr;
  input [9:0] adr_d;
  input [15:0] d_d;
  input en_d;
  input we_d;
  output [15:0] q_d;
  input port_0_rw_ram_ir_internal_RMASK_B_d;
  input port_0_rw_ram_ir_internal_WMASK_B_d;



  // Interconnect Declarations for Component Instantiations 
  assign en = (en_d);
  assign q_d = q;
  assign we = (port_0_rw_ram_ir_internal_WMASK_B_d);
  assign d = (d_d);
  assign adr = (adr_d);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_16_16_10_648_648_16_5_gen
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_16_16_10_648_648_16_5_gen
    (
  en, q, we, d, adr, adr_d, d_d, en_d, we_d, q_d, port_0_rw_ram_ir_internal_RMASK_B_d,
      port_0_rw_ram_ir_internal_WMASK_B_d
);
  output en;
  input [15:0] q;
  output we;
  output [15:0] d;
  output [9:0] adr;
  input [9:0] adr_d;
  input [15:0] d_d;
  input en_d;
  input we_d;
  output [15:0] q_d;
  input port_0_rw_ram_ir_internal_RMASK_B_d;
  input port_0_rw_ram_ir_internal_WMASK_B_d;



  // Interconnect Declarations for Component Instantiations 
  assign en = (en_d);
  assign q_d = q;
  assign we = (port_0_rw_ram_ir_internal_WMASK_B_d);
  assign d = (d_d);
  assign adr = (adr_d);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm
//  FSM Module
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm (
  clk, rst, arst_n, run_wen, fsm_output, VCOL_C_0_tr0, VROW_C_0_tr0
);
  input clk;
  input rst;
  input arst_n;
  input run_wen;
  output [3:0] fsm_output;
  reg [3:0] fsm_output;
  input VCOL_C_0_tr0;
  input VROW_C_0_tr0;


  // FSM State Type Declaration for EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm_1
  parameter
    main_C_0 = 2'd0,
    VCOL_C_0 = 2'd1,
    VROW_C_0 = 2'd2,
    main_C_1 = 2'd3;

  reg [1:0] state_var;
  reg [1:0] state_var_NS;


  // Interconnect Declarations for Component Instantiations 
  always @(*)
  begin : EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm_1
    case (state_var)
      VCOL_C_0 : begin
        fsm_output = 4'b0010;
        if ( VCOL_C_0_tr0 ) begin
          state_var_NS = VROW_C_0;
        end
        else begin
          state_var_NS = VCOL_C_0;
        end
      end
      VROW_C_0 : begin
        fsm_output = 4'b0100;
        if ( VROW_C_0_tr0 ) begin
          state_var_NS = main_C_1;
        end
        else begin
          state_var_NS = VCOL_C_0;
        end
      end
      main_C_1 : begin
        fsm_output = 4'b1000;
        state_var_NS = main_C_0;
      end
      // main_C_0
      default : begin
        fsm_output = 4'b0001;
        state_var_NS = VCOL_C_0;
      end
    endcase
  end

  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      state_var <= main_C_0;
    end
    else if ( rst ) begin
      state_var <= main_C_0;
    end
    else if ( run_wen ) begin
      state_var <= state_var_NS;
    end
  end

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_staller
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_staller (
  clk, rst, arst_n, run_wen, run_wten, dat_in_rsci_wen_comp, dat_out_rsci_wen_comp
);
  input clk;
  input rst;
  input arst_n;
  output run_wen;
  output run_wten;
  reg run_wten;
  input dat_in_rsci_wen_comp;
  input dat_out_rsci_wen_comp;



  // Interconnect Declarations for Component Instantiations 
  assign run_wen = dat_in_rsci_wen_comp & dat_out_rsci_wen_comp;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      run_wten <= 1'b0;
    end
    else if ( rst ) begin
      run_wten <= 1'b0;
    end
    else begin
      run_wten <= ~ run_wen;
    end
  end
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_ctrl_signal_triosy_obj_ctrl_signal_triosy_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_ctrl_signal_triosy_obj_ctrl_signal_triosy_wait_ctrl
    (
  run_wten, ctrl_signal_triosy_obj_iswt0, ctrl_signal_triosy_obj_biwt
);
  input run_wten;
  input ctrl_signal_triosy_obj_iswt0;
  output ctrl_signal_triosy_obj_biwt;



  // Interconnect Declarations for Component Instantiations 
  assign ctrl_signal_triosy_obj_biwt = (~ run_wten) & ctrl_signal_triosy_obj_iswt0;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_wait_dp (
  line_buf0_rsci_en_d, line_buf1_rsci_en_d, run_wen, line_buf0_rsci_cgo, line_buf0_rsci_cgo_ir_unreg,
      line_buf1_rsci_cgo, line_buf1_rsci_cgo_ir_unreg
);
  output line_buf0_rsci_en_d;
  output line_buf1_rsci_en_d;
  input run_wen;
  input line_buf0_rsci_cgo;
  input line_buf0_rsci_cgo_ir_unreg;
  input line_buf1_rsci_cgo;
  input line_buf1_rsci_cgo_ir_unreg;



  // Interconnect Declarations for Component Instantiations 
  assign line_buf0_rsci_en_d = run_wen & (line_buf0_rsci_cgo | line_buf0_rsci_cgo_ir_unreg);
  assign line_buf1_rsci_en_d = run_wen & (line_buf1_rsci_cgo | line_buf1_rsci_cgo_ir_unreg);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_dat_out_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_dat_out_wait_dp (
  clk, rst, arst_n, dat_out_rsci_oswt, dat_out_rsci_wen_comp, dat_out_rsci_biwt,
      dat_out_rsci_bdwt, dat_out_rsci_bcwt
);
  input clk;
  input rst;
  input arst_n;
  input dat_out_rsci_oswt;
  output dat_out_rsci_wen_comp;
  input dat_out_rsci_biwt;
  input dat_out_rsci_bdwt;
  output dat_out_rsci_bcwt;
  reg dat_out_rsci_bcwt;



  // Interconnect Declarations for Component Instantiations 
  assign dat_out_rsci_wen_comp = (~ dat_out_rsci_oswt) | dat_out_rsci_biwt | dat_out_rsci_bcwt;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dat_out_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      dat_out_rsci_bcwt <= 1'b0;
    end
    else begin
      dat_out_rsci_bcwt <= ~((~(dat_out_rsci_bcwt | dat_out_rsci_biwt)) | dat_out_rsci_bdwt);
    end
  end
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_dat_out_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_dat_out_wait_ctrl (
  run_wen, dat_out_rsci_oswt, dat_out_rsci_biwt, dat_out_rsci_bdwt, dat_out_rsci_bcwt,
      dat_out_rsci_irdy, dat_out_rsci_ivld_run_sct
);
  input run_wen;
  input dat_out_rsci_oswt;
  output dat_out_rsci_biwt;
  output dat_out_rsci_bdwt;
  input dat_out_rsci_bcwt;
  input dat_out_rsci_irdy;
  output dat_out_rsci_ivld_run_sct;


  // Interconnect Declarations
  wire dat_out_rsci_ogwt;


  // Interconnect Declarations for Component Instantiations 
  assign dat_out_rsci_bdwt = dat_out_rsci_oswt & run_wen;
  assign dat_out_rsci_biwt = dat_out_rsci_ogwt & dat_out_rsci_irdy;
  assign dat_out_rsci_ogwt = dat_out_rsci_oswt & (~ dat_out_rsci_bcwt);
  assign dat_out_rsci_ivld_run_sct = dat_out_rsci_ogwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_dat_in_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_dat_in_wait_dp (
  clk, rst, arst_n, dat_in_rsci_oswt, dat_in_rsci_wen_comp, dat_in_rsci_idat_mxwt,
      dat_in_rsci_biwt, dat_in_rsci_bdwt, dat_in_rsci_bcwt, dat_in_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  input dat_in_rsci_oswt;
  output dat_in_rsci_wen_comp;
  output [7:0] dat_in_rsci_idat_mxwt;
  input dat_in_rsci_biwt;
  input dat_in_rsci_bdwt;
  output dat_in_rsci_bcwt;
  reg dat_in_rsci_bcwt;
  input [7:0] dat_in_rsci_idat;


  // Interconnect Declarations
  reg [7:0] dat_in_rsci_idat_bfwt;


  // Interconnect Declarations for Component Instantiations 
  assign dat_in_rsci_wen_comp = (~ dat_in_rsci_oswt) | dat_in_rsci_biwt | dat_in_rsci_bcwt;
  assign dat_in_rsci_idat_mxwt = MUX_v_8_2_2(dat_in_rsci_idat, dat_in_rsci_idat_bfwt,
      dat_in_rsci_bcwt);
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dat_in_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      dat_in_rsci_bcwt <= 1'b0;
    end
    else begin
      dat_in_rsci_bcwt <= ~((~(dat_in_rsci_bcwt | dat_in_rsci_biwt)) | dat_in_rsci_bdwt);
    end
  end
  always @(posedge clk) begin
    if ( dat_in_rsci_biwt ) begin
      dat_in_rsci_idat_bfwt <= dat_in_rsci_idat;
    end
  end

  function automatic [7:0] MUX_v_8_2_2;
    input [7:0] input_0;
    input [7:0] input_1;
    input  sel;
    reg [7:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_8_2_2 = result;
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_dat_in_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_dat_in_wait_ctrl (
  run_wen, dat_in_rsci_oswt, dat_in_rsci_biwt, dat_in_rsci_bdwt, dat_in_rsci_bcwt,
      dat_in_rsci_irdy_run_sct, dat_in_rsci_ivld
);
  input run_wen;
  input dat_in_rsci_oswt;
  output dat_in_rsci_biwt;
  output dat_in_rsci_bdwt;
  input dat_in_rsci_bcwt;
  output dat_in_rsci_irdy_run_sct;
  input dat_in_rsci_ivld;


  // Interconnect Declarations
  wire dat_in_rsci_ogwt;


  // Interconnect Declarations for Component Instantiations 
  assign dat_in_rsci_bdwt = dat_in_rsci_oswt & run_wen;
  assign dat_in_rsci_biwt = dat_in_rsci_ogwt & dat_in_rsci_ivld;
  assign dat_in_rsci_ogwt = dat_in_rsci_oswt & (~ dat_in_rsci_bcwt);
  assign dat_in_rsci_irdy_run_sct = dat_in_rsci_ogwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_ctrl_signal_triosy_obj
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_ctrl_signal_triosy_obj (
  ctrl_signal_triosy_lz, run_wten, ctrl_signal_triosy_obj_iswt0
);
  output ctrl_signal_triosy_lz;
  input run_wten;
  input ctrl_signal_triosy_obj_iswt0;


  // Interconnect Declarations
  wire ctrl_signal_triosy_obj_biwt;


  // Interconnect Declarations for Component Instantiations 
  mgc_io_sync_v2 #(.valid(32'sd0)) ctrl_signal_triosy_obj (
      .ld(ctrl_signal_triosy_obj_biwt),
      .lz(ctrl_signal_triosy_lz)
    );
  EdgeDetect_IP_Denoise_IP_run_ctrl_signal_triosy_obj_ctrl_signal_triosy_wait_ctrl
      EdgeDetect_IP_Denoise_IP_run_ctrl_signal_triosy_obj_ctrl_signal_triosy_wait_ctrl_inst
      (
      .run_wten(run_wten),
      .ctrl_signal_triosy_obj_iswt0(ctrl_signal_triosy_obj_iswt0),
      .ctrl_signal_triosy_obj_biwt(ctrl_signal_triosy_obj_biwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_dat_out_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_dat_out_rsci (
  clk, rst, arst_n, dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy, run_wen, dat_out_rsci_oswt,
      dat_out_rsci_wen_comp, dat_out_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  output [7:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  input run_wen;
  input dat_out_rsci_oswt;
  output dat_out_rsci_wen_comp;
  input [7:0] dat_out_rsci_idat;


  // Interconnect Declarations
  wire dat_out_rsci_biwt;
  wire dat_out_rsci_bdwt;
  wire dat_out_rsci_bcwt;
  wire dat_out_rsci_irdy;
  wire dat_out_rsci_ivld_run_sct;


  // Interconnect Declarations for Component Instantiations 
  ccs_out_wait_v1 #(.rscid(32'sd4),
  .width(32'sd8)) dat_out_rsci (
      .irdy(dat_out_rsci_irdy),
      .ivld(dat_out_rsci_ivld_run_sct),
      .idat(dat_out_rsci_idat),
      .rdy(dat_out_rsc_rdy),
      .vld(dat_out_rsc_vld),
      .dat(dat_out_rsc_dat)
    );
  EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_dat_out_wait_ctrl EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_dat_out_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .dat_out_rsci_oswt(dat_out_rsci_oswt),
      .dat_out_rsci_biwt(dat_out_rsci_biwt),
      .dat_out_rsci_bdwt(dat_out_rsci_bdwt),
      .dat_out_rsci_bcwt(dat_out_rsci_bcwt),
      .dat_out_rsci_irdy(dat_out_rsci_irdy),
      .dat_out_rsci_ivld_run_sct(dat_out_rsci_ivld_run_sct)
    );
  EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_dat_out_wait_dp EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_dat_out_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_out_rsci_oswt(dat_out_rsci_oswt),
      .dat_out_rsci_wen_comp(dat_out_rsci_wen_comp),
      .dat_out_rsci_biwt(dat_out_rsci_biwt),
      .dat_out_rsci_bdwt(dat_out_rsci_bdwt),
      .dat_out_rsci_bcwt(dat_out_rsci_bcwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run_dat_in_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run_dat_in_rsci (
  dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, run_wen, dat_in_rsci_oswt, dat_in_rsci_wen_comp,
      dat_in_rsci_idat_mxwt
);
  input [7:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input run_wen;
  input dat_in_rsci_oswt;
  output dat_in_rsci_wen_comp;
  output [7:0] dat_in_rsci_idat_mxwt;


  // Interconnect Declarations
  wire dat_in_rsci_irdy_run_sct;
  wire dat_in_rsci_ivld;
  wire [7:0] dat_in_rsci_idat;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_wait_coupled_v1 #(.rscid(32'sd1),
  .width(32'sd8)) dat_in_rsci (
      .rdy(dat_in_rsc_rdy),
      .vld(dat_in_rsc_vld),
      .dat(dat_in_rsc_dat),
      .irdy(dat_in_rsci_irdy_run_sct),
      .ivld(dat_in_rsci_ivld),
      .idat(dat_in_rsci_idat)
    );
  EdgeDetect_IP_Denoise_IP_run_dat_in_rsci_dat_in_wait_ctrl EdgeDetect_IP_Denoise_IP_run_dat_in_rsci_dat_in_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .dat_in_rsci_iswt0(dat_in_rsci_oswt),
      .dat_in_rsci_irdy_run_sct(dat_in_rsci_irdy_run_sct)
    );
  assign dat_in_rsci_idat_mxwt = dat_in_rsci_idat;
  assign dat_in_rsci_wen_comp = (~ dat_in_rsci_oswt) | dat_in_rsci_ivld;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_ctrl_signal_triosy_obj
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_ctrl_signal_triosy_obj (
  ctrl_signal_triosy_lz, run_wten, ctrl_signal_triosy_obj_iswt0
);
  output ctrl_signal_triosy_lz;
  input run_wten;
  input ctrl_signal_triosy_obj_iswt0;


  // Interconnect Declarations
  wire ctrl_signal_triosy_obj_biwt;


  // Interconnect Declarations for Component Instantiations 
  mgc_io_sync_v2 #(.valid(32'sd0)) ctrl_signal_triosy_obj (
      .ld(ctrl_signal_triosy_obj_biwt),
      .lz(ctrl_signal_triosy_lz)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_ctrl_signal_triosy_obj_ctrl_signal_triosy_wait_ctrl
      EdgeDetect_IP_EdgeDetect_Filter_run_ctrl_signal_triosy_obj_ctrl_signal_triosy_wait_ctrl_inst
      (
      .run_wten(run_wten),
      .ctrl_signal_triosy_obj_iswt0(ctrl_signal_triosy_obj_iswt0),
      .ctrl_signal_triosy_obj_biwt(ctrl_signal_triosy_obj_biwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci (
  clk, rst, arst_n, dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy, run_wen, dat_out_rsci_oswt,
      dat_out_rsci_wen_comp, dat_out_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  output [7:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  input run_wen;
  input dat_out_rsci_oswt;
  output dat_out_rsci_wen_comp;
  input [7:0] dat_out_rsci_idat;


  // Interconnect Declarations
  wire dat_out_rsci_biwt;
  wire dat_out_rsci_bdwt;
  wire dat_out_rsci_bcwt;
  wire dat_out_rsci_irdy;
  wire dat_out_rsci_ivld_run_sct;


  // Interconnect Declarations for Component Instantiations 
  ccs_out_wait_v1 #(.rscid(32'sd14),
  .width(32'sd8)) dat_out_rsci (
      .irdy(dat_out_rsci_irdy),
      .ivld(dat_out_rsci_ivld_run_sct),
      .idat(dat_out_rsci_idat),
      .rdy(dat_out_rsc_rdy),
      .vld(dat_out_rsc_vld),
      .dat(dat_out_rsc_dat)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_dat_out_wait_ctrl EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_dat_out_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .dat_out_rsci_oswt(dat_out_rsci_oswt),
      .dat_out_rsci_biwt(dat_out_rsci_biwt),
      .dat_out_rsci_bdwt(dat_out_rsci_bdwt),
      .dat_out_rsci_bcwt(dat_out_rsci_bcwt),
      .dat_out_rsci_irdy(dat_out_rsci_irdy),
      .dat_out_rsci_ivld_run_sct(dat_out_rsci_ivld_run_sct)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_dat_out_wait_dp EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_dat_out_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_out_rsci_oswt(dat_out_rsci_oswt),
      .dat_out_rsci_wen_comp(dat_out_rsci_wen_comp),
      .dat_out_rsci_biwt(dat_out_rsci_biwt),
      .dat_out_rsci_bdwt(dat_out_rsci_bdwt),
      .dat_out_rsci_bcwt(dat_out_rsci_bcwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci (
  clk, rst, arst_n, dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, run_wen, dat_in_rsci_oswt,
      dat_in_rsci_wen_comp, dat_in_rsci_idat_mxwt
);
  input clk;
  input rst;
  input arst_n;
  input [7:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input run_wen;
  input dat_in_rsci_oswt;
  output dat_in_rsci_wen_comp;
  output [7:0] dat_in_rsci_idat_mxwt;


  // Interconnect Declarations
  wire dat_in_rsci_biwt;
  wire dat_in_rsci_bdwt;
  wire dat_in_rsci_bcwt;
  wire dat_in_rsci_irdy_run_sct;
  wire dat_in_rsci_ivld;
  wire [7:0] dat_in_rsci_idat;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_wait_v1 #(.rscid(32'sd11),
  .width(32'sd8)) dat_in_rsci (
      .rdy(dat_in_rsc_rdy),
      .vld(dat_in_rsc_vld),
      .dat(dat_in_rsc_dat),
      .irdy(dat_in_rsci_irdy_run_sct),
      .ivld(dat_in_rsci_ivld),
      .idat(dat_in_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_dat_in_wait_ctrl EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_dat_in_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .dat_in_rsci_oswt(dat_in_rsci_oswt),
      .dat_in_rsci_biwt(dat_in_rsci_biwt),
      .dat_in_rsci_bdwt(dat_in_rsci_bdwt),
      .dat_in_rsci_bcwt(dat_in_rsci_bcwt),
      .dat_in_rsci_irdy_run_sct(dat_in_rsci_irdy_run_sct),
      .dat_in_rsci_ivld(dat_in_rsci_ivld)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_dat_in_wait_dp EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_dat_in_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_in_rsci_oswt(dat_in_rsci_oswt),
      .dat_in_rsci_wen_comp(dat_in_rsci_wen_comp),
      .dat_in_rsci_idat_mxwt(dat_in_rsci_idat_mxwt),
      .dat_in_rsci_biwt(dat_in_rsci_biwt),
      .dat_in_rsci_bdwt(dat_in_rsci_bdwt),
      .dat_in_rsci_bcwt(dat_in_rsci_bcwt),
      .dat_in_rsci_idat(dat_in_rsci_idat)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP_run
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP_run (
  clk, rst, arst_n, dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, widthIn, heightIn,
      dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy, ctrl_signal_triosy_lz, ctrl_signal_rsci_idat,
      line_buf0_rsci_d_d, line_buf0_rsci_en_d, line_buf0_rsci_q_d, line_buf1_rsci_d_d,
      line_buf1_rsci_en_d, line_buf1_rsci_q_d, line_buf0_rsci_adr_d_pff, line_buf0_rsci_we_d_pff,
      line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_pff, line_buf1_rsci_we_d_pff
);
  input clk;
  input rst;
  input arst_n;
  input [7:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input [10:0] widthIn;
  input [9:0] heightIn;
  output [7:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  output ctrl_signal_triosy_lz;
  input [1:0] ctrl_signal_rsci_idat;
  output [15:0] line_buf0_rsci_d_d;
  output line_buf0_rsci_en_d;
  input [15:0] line_buf0_rsci_q_d;
  output [15:0] line_buf1_rsci_d_d;
  output line_buf1_rsci_en_d;
  input [15:0] line_buf1_rsci_q_d;
  output [9:0] line_buf0_rsci_adr_d_pff;
  output line_buf0_rsci_we_d_pff;
  output line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_pff;
  output line_buf1_rsci_we_d_pff;


  // Interconnect Declarations
  wire run_wen;
  wire run_wten;
  wire dat_in_rsci_wen_comp;
  wire [7:0] dat_in_rsci_idat_mxwt;
  wire dat_out_rsci_wen_comp;
  reg [7:0] dat_out_rsci_idat;
  reg ctrl_signal_triosy_obj_iswt0;
  wire [3:0] fsm_output;
  wire VROW_equal_tmp;
  wire operator_11_false_4_operator_11_false_4_nor_tmp;
  wire operator_11_false_1_nor_tmp;
  wire VCOL_else_4_else_else_else_nor_1_tmp;
  wire VCOL_else_4_else_aif_equal_tmp;
  wire VCOL_VCOL_oelse_operator_11_false_or_tmp;
  wire and_dcpl_1;
  wire and_dcpl_4;
  wire or_dcpl_4;
  wire mux_tmp_8;
  wire or_tmp_20;
  wire mux_tmp_16;
  wire or_tmp_41;
  wire and_dcpl_16;
  wire or_dcpl_40;
  wire and_dcpl_25;
  wire mux_tmp_236;
  wire nor_tmp_55;
  wire and_dcpl_51;
  wire and_dcpl_53;
  wire VCOL_else_5_if_for_mux_78_tmp_0;
  wire lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_3_1_1;
  wire VCOL_else_5_if_for_and_14_ssc_1;
  wire VCOL_equal_tmp_7;
  wire VCOL_equal_tmp_5;
  wire VCOL_equal_tmp_6;
  wire exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_2;
  wire VCOL_else_5_if_for_equal_tmp_mx0w1;
  wire lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_0_mx0w1;
  wire lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1_mx1;
  wire lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_mx0w0;
  wire lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0_mx1;
  wire operator_10_false_1_operator_10_false_1_and_cse_sva_1;
  wire lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0;
  wire VCOL_and_16_cse_1;
  reg VCOL_equal_tmp_3_1;
  reg VCOL_equal_tmp_2_1;
  reg lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3;
  reg pix_result_11_lpi_3;
  reg lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  reg [7:0] pix_result_10_3_lpi_3;
  reg [1:0] pix_result_2_1_lpi_3;
  reg pix_result_0_lpi_3;
  wire VCOL_else_4_else_else_else_unequal_tmp_1;
  wire VCOL_or_9_tmp_1;
  reg exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  reg operator_10_false_1_operator_10_false_1_and_cse_sva_1_1;
  wire VCOL_VCOL_nor_1_m1c_1;
  reg VCOL_land_1_lpi_3_dfm_1;
  wire VCOL_else_5_if_for_and_9_m1c_1;
  wire VCOL_else_4_VCOL_else_4_nor_1_m1c_1;
  wire VCOL_VCOL_nor_5_m1c_1;
  wire VCOL_or_tmp_1;
  wire VCOL_else_4_else_else_else_and_tmp_1;
  wire VCOL_and_m1c_1;
  reg operator_11_false_4_operator_11_false_4_nor_cse_sva_1;
  wire VCOL_else_4_else_else_VCOL_else_4_else_else_nor_3_cse_1;
  wire VCOL_else_4_else_else_else_else_and_5_tmp_1;
  wire VCOL_else_4_else_else_and_3_m1c_1;
  reg VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1;
  reg operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1;
  reg exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  wire VCOL_else_5_else_if_for_1_and_stg_2_0_sva_1;
  reg max_i_3_lpi_3_dfm_1_1;
  reg VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  wire VCOL_else_5_else_if_for_and_stg_2_0_sva_1;
  wire VCOL_else_5_else_if_for_1_and_stg_1_3_sva_1;
  wire VCOL_else_5_else_if_for_and_stg_1_3_sva_1;
  wire VCOL_else_5_else_if_for_1_and_stg_1_2_sva_1;
  wire VCOL_else_5_else_if_for_and_stg_1_2_sva_1;
  wire VCOL_else_5_else_if_for_1_and_stg_1_1_sva_1;
  wire VCOL_else_5_else_if_for_and_stg_1_1_sva_1;
  wire VCOL_else_5_else_if_for_1_and_stg_1_0_sva_1;
  wire VCOL_else_5_else_if_for_and_stg_1_0_sva_1;
  wire [2:0] operator_4_false_acc_psp_sva_1;
  wire [3:0] nl_operator_4_false_acc_psp_sva_1;
  wire [3:0] i_1_lpi_3_dfm_2;
  wire max_i_3_lpi_3_mx1;
  reg VCOL_stage_0_2;
  reg [9:0] VROW_y_sva;
  reg [10:0] VCOL_x_sva;
  reg VCOL_stage_0_1;
  reg [1:0] VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1;
  reg lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1;
  reg lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0;
  reg lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1;
  reg lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0;
  reg [3:0] i_1_lpi_3_dfm_1_1;
  reg [3:0] i_lpi_3_dfm_2_1;
  reg max_i_3_lpi_3_dfm_3_1;
  reg exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1;
  reg exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3;
  reg VCOL_if_6_VCOL_if_6_and_itm_1;
  reg [9:0] VCOL_else_3_else_asn_itm_1;
  reg operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1;
  wire pix_result_11_lpi_3_dfm_3_mx1w0;
  wire [7:0] pix_result_10_3_lpi_3_dfm_3_mx1w0;
  wire [1:0] pix_result_2_1_lpi_3_dfm_3_mx1w0;
  wire pix_result_0_lpi_3_dfm_3_mx1w0;
  wire [1:0] VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1_mx0;
  wire [10:0] VCOL_x_sva_mx1;
  wire or_72_cse;
  reg reg_line_buf1_rsci_cgo_ir_cse;
  reg reg_line_buf0_rsci_cgo_ir_cse;
  reg reg_dat_out_rsci_iswt0_cse;
  reg reg_dat_in_rsci_iswt0_cse;
  wire VCOL_and_79_cse;
  reg reg_operator_11_false_6_nor_itm_1_cse;
  reg [7:0] reg_max_val_10_3_lpi_3_dfm_1_1_cse;
  wire [7:0] VCOL_else_5_if_for_mux_87_cse;
  wire mux_262_cse;
  wire mux_231_cse;
  wire nor_16_cse;
  wire VCOL_if_6_VCOL_if_6_or_cse;
  wire mux_36_cse;
  wire VCOL_and_46_tmp;
  wire mux_256_cse;
  wire exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1;
  wire j_and_1_rgt;
  wire and_217_m1c;
  wire nor_85_cse;
  wire j_2_0_lpi_3_dfm_3_1_mx1c0;
  wire VCOL_aelse_VCOL_aelse_and_cse;
  wire VCOL_x_and_cse;
  wire [3:0] i_1_sva_1_mx0w0;
  wire [4:0] nl_i_1_sva_1_mx0w0;
  wire and_133_rmff;
  wire and_131_rmff;
  reg [7:0] VCOL_VCOL_slc_pix_39_32_2_lpi_4;
  wire [7:0] VCOL_VCOL_slc_pix_39_32_2_lpi_3_dfm_mx1w0;
  reg [7:0] VCOL_VCOL_slc_pix_63_56_lpi_4;
  wire [7:0] pix_4_lpi_3_dfm_1_mx0;
  reg [7:0] VCOL_VCOL_slc_pix_47_40_2_lpi_4;
  wire [7:0] pix_2_lpi_3_dfm_9_mx1w0;
  reg [7:0] VCOL_VCOL_slc_pix_71_64_lpi_4;
  wire VCOL_and_42_cse;
  reg VCOL_equal_tmp_1;
  reg exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1;
  wire VCOL_and_6_m1c_1;
  wire VCOL_or_1_cse_1;
  wire VCOL_and_41_cse;
  wire j_or_1_itm;
  wire mux_263_itm;
  wire mux_tmp;
  wire or_tmp_386;
  wire [9:0] z_out;
  wire [10:0] nl_z_out;
  reg [7:0] pix_0_lpi_3;
  reg [7:0] pix_1_lpi_3;
  reg [7:0] pix_2_lpi_3;
  reg [15:0] rdbuf0_pix_lpi_3;
  reg [15:0] rdbuf1_pix_lpi_3;
  reg [7:0] pix_4_lpi_3;
  reg [7:0] pix_3_lpi_3;
  reg [7:0] pix_6_lpi_3;
  reg [7:0] pix_7_lpi_3;
  reg [7:0] pix_8_lpi_3;
  reg [7:0] pix_5_lpi_3;
  reg [7:0] tmp_pix_4_lpi_3;
  reg [7:0] tmp_pix_3_lpi_3;
  reg [7:0] tmp_pix_5_lpi_3;
  reg [7:0] tmp_pix_2_lpi_3;
  reg [7:0] tmp_pix_6_lpi_3;
  reg [7:0] tmp_pix_1_lpi_3;
  reg [7:0] tmp_pix_7_lpi_3;
  reg [7:0] tmp_pix_0_lpi_3;
  reg [7:0] tmp_pix_8_lpi_3;
  reg [7:0] VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1;
  reg VCOL_land_lpi_3_dfm_1;
  reg VCOL_equal_tmp_1_1;
  reg [7:0] VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_2_1;
  reg VCOL_and_37_itm_1;
  wire lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_mx0c1;
  wire VCOL_else_5_if_for_mux_68_mx0w0;
  wire j_2_0_lpi_3_dfm_3_1_mx1c3;
  wire [3:0] i_sva_2;
  wire [4:0] nl_i_sva_2;
  wire [7:0] pix_0_lpi_3_dfm_10_mx1w0;
  wire [7:0] pix_1_lpi_3_dfm_10_mx1w0;
  wire [7:0] tmp_pix_1_lpi_3_mx1;
  wire [7:0] tmp_pix_1_lpi_3_dfm_2_mx2w1;
  wire [7:0] tmp_pix_5_lpi_3_mx1;
  wire [7:0] tmp_pix_5_lpi_3_dfm_2_mx2w1;
  wire [7:0] tmp_pix_2_lpi_3_mx1;
  wire [7:0] tmp_pix_2_lpi_3_dfm_2_mx2w1;
  wire [7:0] tmp_pix_6_lpi_3_dfm_2_mx2w1;
  wire [7:0] tmp_pix_3_lpi_3_mx1;
  wire [7:0] tmp_pix_3_lpi_3_dfm_2_mx2w1;
  wire [7:0] tmp_pix_7_lpi_3_dfm_2_mx2w1;
  wire [7:0] tmp_pix_0_lpi_3_mx0;
  wire [7:0] tmp_pix_8_lpi_3_dfm_2_mx2w1;
  wire [7:0] tmp_pix_4_lpi_3_mx1;
  wire [7:0] tmp_pix_4_lpi_3_dfm_2_mx2w1;
  wire max_i_3_lpi_3_dfm_1_1_mx0;
  wire [7:0] pix_3_lpi_3_dfm_mx0;
  wire [7:0] pix_4_lpi_3_dfm_mx0;
  wire [7:0] pix_1_lpi_3_dfm_11;
  wire [7:0] pix_7_lpi_3_dfm_5_mx0;
  wire VCOL_else_4_else_else_or_6_m1c_1;
  wire VCOL_else_4_else_else_and_7_m1c_1;
  wire VCOL_lor_lpi_3_dfm_1;
  wire [12:0] VCOL_else_5_if_for_acc_psp_sva_1;
  wire [13:0] nl_VCOL_else_5_if_for_acc_psp_sva_1;
  wire [7:0] pix_3_lpi_3_dfm_11;
  wire [7:0] pix_6_lpi_3_dfm_9;
  wire [7:0] pix_8_lpi_3_dfm_8;
  wire [10:0] VCOL_x_sva_2;
  wire [11:0] nl_VCOL_x_sva_2;
  wire VCOL_else_4_and_3_cse_1;
  wire VCOL_else_5_if_for_and_49_cse_1;
  wire VCOL_else_5_if_for_and_51_cse_1;
  wire VCOL_else_5_if_for_and_66_m1c_1;
  wire VCOL_else_5_if_for_and_50_m1c_1;
  wire VCOL_or_7_tmp_1;
  wire VCOL_else_5_if_for_or_m1c_1;
  wire [7:0] max_val_10_3_lpi_3_dfm_mx0;
  wire [7:0] VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_sva_1;
  wire [7:0] operator_12_9_false_AC_TRN_AC_SAT_8_false_slc_tmp_pix_8_7_0_cse_sva_1;
  wire VCOL_else_5_else_if_for_and_20_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_8_tmp_1;
  wire VCOL_else_5_else_if_for_and_18_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_7_tmp_1;
  wire VCOL_else_5_else_if_for_and_16_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_6_tmp_1;
  wire VCOL_else_5_else_if_for_and_14_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_5_tmp_1;
  wire VCOL_else_5_else_if_for_and_12_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_4_tmp_1;
  wire VCOL_else_5_else_if_for_and_13_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_3_tmp_1;
  wire VCOL_else_5_else_if_for_and_15_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_2_tmp_1;
  wire VCOL_else_5_else_if_for_and_17_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_1_tmp_1;
  wire VCOL_else_5_else_if_for_and_19_tmp_1;
  wire VCOL_else_5_else_if_for_1_for_and_tmp_1;
  wire j_2_0_lpi_3_dfm_3_1_mx0w0_0;
  wire i_lpi_3_dfm_mx0_3;
  wire [2:0] i_lpi_3_dfm_mx0_2_0;
  reg [1:0] j_2_0_lpi_3_dfm_3_1_rsp_0;
  reg j_2_0_lpi_3_dfm_3_1_rsp_1;
  wire VROW_y_or_cse;
  wire max_i_or_m1c;
  reg [3:0] reg_i_1_lpi_3_dfm_1_cse;
  wire [7:0] operator_8_false_mux_cse;
  reg [1:0] max_i_2_0_lpi_3_dfm_1_1_2_1;
  reg max_i_2_0_lpi_3_dfm_1_1_0;
  wire operator_10_false_1_and_cse;
  wire rdbuf1_pix_and_1_cse;
  wire operator_11_false_6_and_cse;
  wire pix_result_and_cse;
  wire and_dcpl_66;
  wire and_dcpl_91;
  wire or_tmp_428;
  wire nand_tmp_18;
  wire mux_tmp_299;
  wire mux_tmp_309;
  wire mux_tmp_317;
  wire mux_tmp_321;
  wire nand_tmp_22;
  wire mux_tmp_329;
  wire mux_tmp_333;
  wire or_tmp_477;
  wire and_tmp_25;
  wire not_tmp_284;
  wire or_tmp_484;
  wire not_tmp_287;
  wire nand_tmp_25;
  wire mux_tmp_348;
  wire or_tmp_497;
  wire or_tmp_501;
  wire or_tmp_504;
  wire not_tmp_297;
  wire or_tmp_507;
  wire and_dcpl_123;
  wire or_tmp_514;
  wire mux_tmp_373;
  wire mux_tmp_378;
  wire nand_tmp_28;
  wire or_tmp_530;
  wire mux_tmp_388;
  wire mux_tmp_393;
  wire or_tmp_540;
  wire mux_tmp_402;
  wire mux_tmp_407;
  wire nand_tmp_35;
  wire mux_tmp_416;
  wire mux_tmp_421;
  wire or_tmp_574;
  wire not_tmp_319;
  wire mux_tmp_431;
  wire or_tmp_599;
  wire mux_tmp_445;
  wire mux_tmp_450;
  wire or_tmp_609;
  wire mux_tmp_459;
  wire nand_tmp_44;
  wire nand_tmp_45;
  wire mux_tmp_469;
  wire mux_tmp_471;
  wire nand_tmp_46;
  wire mux_tmp_481;
  wire mux_tmp_486;
  wire or_tmp_659;
  wire mux_tmp_495;
  wire and_272_cse;
  wire and_281_cse;
  wire or_479_cse;
  wire or_325_cse;
  wire nand_114_cse;
  wire nand_116_cse;
  wire or_500_cse;
  wire or_522_cse;
  wire or_501_cse;
  wire or_587_cse;
  wire mux_242_cse;
  wire or_774_cse;
  wire or_612_cse;
  wire nor_187_cse;
  wire nor_186_cse;
  wire nor_272_cse;
  wire nor_196_cse;
  wire nor_270_cse;
  wire and_396_cse;
  wire and_397_cse;
  wire and_431_cse;
  wire nand_110_cse;
  wire nand_142_cse;
  wire or_775_cse;
  wire or_564_cse;
  wire or_593_cse;
  wire or_495_cse;
  wire nor_238_cse;
  wire nor_148_cse;
  wire and_429_cse;
  wire VCOL_else_5_if_for_and_6_cse;
  wire nand_112_cse;
  wire nor_211_cse;
  wire nor_319_cse;
  wire mux_307_cse;
  wire and_384_cse;
  wire mux_372_cse;
  wire nor_289_cse;
  wire operator_4_false_3_acc_itm_4;
  wire operator_10_false_acc_itm_10_1;
  wire operator_4_false_acc_itm_3;
  wire [8:0] operator_8_false_mul_itm_9_1_1;
  wire operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8;
  wire operator_4_false_2_acc_itm_2;
  wire operator_11_false_acc_itm_11_1;

  wire not_687_nl;
  wire VROW_y_not_2_nl;
  wire[12:0] operator_12_9_false_AC_TRN_AC_SAT_acc_nl;
  wire[13:0] nl_operator_12_9_false_AC_TRN_AC_SAT_acc_nl;
  wire mux_274_nl;
  wire nor_nl;
  wire mux_273_nl;
  wire mux_272_nl;
  wire nand_100_nl;
  wire or_772_nl;
  wire nor_240_nl;
  wire mux_nl;
  wire nor_239_nl;
  wire nand_56_nl;
  wire and_115_nl;
  wire and_117_nl;
  wire mux_227_nl;
  wire mux_223_nl;
  wire mux_222_nl;
  wire and_119_nl;
  wire mux_228_nl;
  wire and_251_nl;
  wire nor_111_nl;
  wire mux_283_nl;
  wire mux_282_nl;
  wire or_480_nl;
  wire mux_280_nl;
  wire mux_279_nl;
  wire and_nl;
  wire nor_246_nl;
  wire mux_284_nl;
  wire VCOL_mux_35_nl;
  wire VCOL_else_5_if_for_VCOL_else_5_if_for_nor_nl;
  wire operator_11_false_mux_nl;
  wire mux_58_nl;
  wire mux_57_nl;
  wire mux_55_nl;
  wire mux_229_nl;
  wire nand_57_nl;
  wire nor_115_nl;
  wire nor_116_nl;
  wire mux_291_nl;
  wire mux_290_nl;
  wire nand_108_nl;
  wire mux_289_nl;
  wire mux_288_nl;
  wire nand_109_nl;
  wire or_493_nl;
  wire mux_292_nl;
  wire nor_255_nl;
  wire mux_254_nl;
  wire and_71_nl;
  wire mux_253_nl;
  wire mux_252_nl;
  wire and_253_nl;
  wire or_452_nl;
  wire mux_251_nl;
  wire nand_15_nl;
  wire or_347_nl;
  wire mux_255_nl;
  wire and_254_nl;
  wire or_352_nl;
  wire mux_295_nl;
  wire mux_294_nl;
  wire mux_293_nl;
  wire or_503_nl;
  wire or_502_nl;
  wire and_169_nl;
  wire mux_299_nl;
  wire mux_298_nl;
  wire mux_297_nl;
  wire nor_256_nl;
  wire mux_296_nl;
  wire or_507_nl;
  wire nand_66_nl;
  wire or_505_nl;
  wire mux_305_nl;
  wire mux_304_nl;
  wire and_400_nl;
  wire mux_303_nl;
  wire nor_145_nl;
  wire mux_15_nl;
  wire mux_12_nl;
  wire mux_306_nl;
  wire or_521_nl;
  wire or_520_nl;
  wire nor_150_nl;
  wire mux_317_nl;
  wire and_409_nl;
  wire mux_316_nl;
  wire mux_315_nl;
  wire mux_314_nl;
  wire nor_258_nl;
  wire mux_313_nl;
  wire and_402_nl;
  wire and_407_nl;
  wire mux_310_nl;
  wire mux_309_nl;
  wire nor_259_nl;
  wire mux_308_nl;
  wire and_405_nl;
  wire and_408_nl;
  wire mux_329_nl;
  wire and_418_nl;
  wire mux_328_nl;
  wire mux_327_nl;
  wire mux_326_nl;
  wire nor_260_nl;
  wire mux_325_nl;
  wire and_411_nl;
  wire and_416_nl;
  wire mux_323_nl;
  wire mux_322_nl;
  wire nor_261_nl;
  wire mux_321_nl;
  wire and_414_nl;
  wire and_417_nl;
  wire mux_341_nl;
  wire and_427_nl;
  wire mux_340_nl;
  wire mux_339_nl;
  wire mux_338_nl;
  wire nor_262_nl;
  wire mux_337_nl;
  wire and_420_nl;
  wire and_425_nl;
  wire mux_335_nl;
  wire mux_334_nl;
  wire nor_263_nl;
  wire mux_333_nl;
  wire and_423_nl;
  wire and_426_nl;
  wire mux_350_nl;
  wire mux_349_nl;
  wire nor_264_nl;
  wire nor_265_nl;
  wire mux_348_nl;
  wire mux_347_nl;
  wire mux_346_nl;
  wire mux_345_nl;
  wire mux_344_nl;
  wire or_572_nl;
  wire or_567_nl;
  wire mux_343_nl;
  wire nor_267_nl;
  wire mux_342_nl;
  wire nand_73_nl;
  wire or_563_nl;
  wire or_560_nl;
  wire mux_360_nl;
  wire mux_359_nl;
  wire and_323_nl;
  wire mux_358_nl;
  wire mux_357_nl;
  wire mux_356_nl;
  wire mux_355_nl;
  wire mux_354_nl;
  wire mux_353_nl;
  wire mux_352_nl;
  wire mux_365_nl;
  wire mux_364_nl;
  wire mux_363_nl;
  wire or_585_nl;
  wire mux_362_nl;
  wire mux_361_nl;
  wire or_584_nl;
  wire or_583_nl;
  wire mux_32_nl;
  wire nor_67_nl;
  wire nor_68_nl;
  wire mux_249_nl;
  wire mux_247_nl;
  wire mux_40_nl;
  wire mux_37_nl;
  wire or_52_nl;
  wire mux_368_nl;
  wire mux_367_nl;
  wire mux_366_nl;
  wire mux_371_nl;
  wire mux_370_nl;
  wire and_335_nl;
  wire and_334_nl;
  wire mux_49_nl;
  wire mux_48_nl;
  wire nor_79_nl;
  wire mux_47_nl;
  wire or_438_nl;
  wire nor_82_nl;
  wire nor_271_nl;
  wire mux_374_nl;
  wire mux_389_nl;
  wire mux_388_nl;
  wire mux_387_nl;
  wire mux_386_nl;
  wire mux_385_nl;
  wire or_783_nl;
  wire mux_384_nl;
  wire mux_383_nl;
  wire mux_382_nl;
  wire or_611_nl;
  wire or_609_nl;
  wire or_604_nl;
  wire or_603_nl;
  wire nor_185_nl;
  wire mux_404_nl;
  wire mux_403_nl;
  wire mux_402_nl;
  wire mux_401_nl;
  wire mux_400_nl;
  wire or_629_nl;
  wire mux_399_nl;
  wire mux_398_nl;
  wire mux_397_nl;
  wire or_627_nl;
  wire or_625_nl;
  wire or_620_nl;
  wire or_619_nl;
  wire nor_190_nl;
  wire mux_418_nl;
  wire mux_417_nl;
  wire mux_416_nl;
  wire mux_415_nl;
  wire mux_414_nl;
  wire or_647_nl;
  wire or_646_nl;
  wire or_645_nl;
  wire or_644_nl;
  wire mux_413_nl;
  wire mux_412_nl;
  wire mux_411_nl;
  wire or_784_nl;
  wire or_630_nl;
  wire mux_432_nl;
  wire mux_431_nl;
  wire mux_430_nl;
  wire mux_429_nl;
  wire mux_428_nl;
  wire or_665_nl;
  wire or_664_nl;
  wire or_663_nl;
  wire or_662_nl;
  wire mux_427_nl;
  wire mux_426_nl;
  wire mux_425_nl;
  wire or_654_nl;
  wire or_648_nl;
  wire mux_446_nl;
  wire mux_445_nl;
  wire mux_444_nl;
  wire mux_443_nl;
  wire mux_442_nl;
  wire or_683_nl;
  wire mux_441_nl;
  wire or_682_nl;
  wire or_681_nl;
  wire nor_213_nl;
  wire nor_212_nl;
  wire mux_440_nl;
  wire mux_439_nl;
  wire mux_438_nl;
  wire mux_437_nl;
  wire mux_436_nl;
  wire or_679_nl;
  wire or_785_nl;
  wire mux_435_nl;
  wire or_676_nl;
  wire or_675_nl;
  wire nand_87_nl;
  wire or_671_nl;
  wire mux_461_nl;
  wire mux_460_nl;
  wire mux_459_nl;
  wire mux_458_nl;
  wire mux_457_nl;
  wire or_698_nl;
  wire mux_456_nl;
  wire mux_455_nl;
  wire mux_454_nl;
  wire or_696_nl;
  wire or_694_nl;
  wire or_689_nl;
  wire or_688_nl;
  wire and_434_nl;
  wire mux_471_nl;
  wire mux_470_nl;
  wire or_712_nl;
  wire or_711_nl;
  wire mux_469_nl;
  wire mux_468_nl;
  wire mux_467_nl;
  wire or_700_nl;
  wire or_699_nl;
  wire mux_483_nl;
  wire mux_482_nl;
  wire mux_481_nl;
  wire mux_480_nl;
  wire mux_479_nl;
  wire or_732_nl;
  wire or_731_nl;
  wire mux_478_nl;
  wire or_730_nl;
  wire or_729_nl;
  wire or_728_nl;
  wire mux_477_nl;
  wire mux_476_nl;
  wire mux_475_nl;
  wire or_721_nl;
  wire or_713_nl;
  wire mux_497_nl;
  wire mux_496_nl;
  wire mux_495_nl;
  wire mux_494_nl;
  wire mux_493_nl;
  wire or_749_nl;
  wire or_748_nl;
  wire or_747_nl;
  wire or_746_nl;
  wire mux_492_nl;
  wire mux_491_nl;
  wire mux_490_nl;
  wire or_738_nl;
  wire or_nl;
  wire mux_501_nl;
  wire nor_280_nl;
  wire mux_500_nl;
  wire nor_277_nl;
  wire mux_499_nl;
  wire or_786_nl;
  wire nand_139_nl;
  wire nor_278_nl;
  wire mux_503_nl;
  wire mux_502_nl;
  wire and_439_nl;
  wire VCOL_else_5_if_for_mux_85_nl;
  wire VCOL_else_5_else_if_for_VCOL_else_5_else_if_for_or_nl;
  wire mux_216_nl;
  wire max_i_or_nl;
  wire max_i_and_2_nl;
  wire max_i_and_1_nl;
  wire mux_250_nl;
  wire nor_126_nl;
  wire nor_127_nl;
  wire VCOL_else_5_if_for_and_44_nl;
  wire VCOL_else_5_if_for_and_48_nl;
  wire VCOL_else_5_if_for_or_9_nl;
  wire VCOL_else_5_if_for_or_10_nl;
  wire VCOL_else_5_if_for_or_11_nl;
  wire VCOL_else_5_if_for_or_12_nl;
  wire VCOL_else_5_if_for_and_65_nl;
  wire VCOL_else_5_if_for_nand_12_nl;
  wire VCOL_else_5_if_for_and_61_nl;
  wire VCOL_and_35_nl;
  wire VCOL_else_5_if_for_and_62_nl;
  wire VCOL_else_5_if_for_and_53_nl;
  wire VCOL_else_5_if_for_or_6_nl;
  wire VCOL_and_38_nl;
  wire VCOL_else_5_if_for_and_63_nl;
  wire VCOL_else_5_if_for_and_64_nl;
  wire VCOL_mux1h_20_nl;
  wire VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_3_nl;
  wire VCOL_else_5_if_for_VCOL_else_5_if_for_and_3_nl;
  wire VCOL_else_5_if_for_mux_73_nl;
  wire[7:0] VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_1_nl;
  wire VCOL_or_2_nl;
  wire[1:0] mux_270_nl;
  wire[1:0] VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_nl;
  wire nor_133_nl;
  wire nor_135_nl;
  wire VCOL_mux1h_23_nl;
  wire VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_2_nl;
  wire VCOL_else_5_if_for_VCOL_else_5_if_for_and_5_nl;
  wire VCOL_or_11_nl;
  wire VCOL_else_5_if_for_and_18_nl;
  wire VCOL_and_54_nl;
  wire VCOL_or_15_nl;
  wire VCOL_else_5_if_for_and_26_nl;
  wire VCOL_and_62_nl;
  wire VCOL_or_12_nl;
  wire VCOL_else_5_if_for_and_20_nl;
  wire VCOL_and_56_nl;
  wire VCOL_or_16_nl;
  wire VCOL_else_5_if_for_and_28_nl;
  wire VCOL_and_64_nl;
  wire VCOL_or_13_nl;
  wire VCOL_else_5_if_for_and_22_nl;
  wire VCOL_and_58_nl;
  wire VCOL_or_17_nl;
  wire VCOL_else_5_if_for_and_30_nl;
  wire VCOL_and_66_nl;
  wire tmp_pix_nand_nl;
  wire VCOL_else_5_if_for_and_16_nl;
  wire VCOL_and_52_nl;
  wire VCOL_or_18_nl;
  wire VCOL_else_5_if_for_and_32_nl;
  wire VCOL_and_68_nl;
  wire VCOL_or_14_nl;
  wire VCOL_else_5_if_for_and_24_nl;
  wire VCOL_and_60_nl;
  wire VCOL_else_5_else_if_for_1_for_VCOL_else_5_else_if_for_1_for_and_3_nl;
  wire[4:0] operator_4_false_3_acc_nl;
  wire[5:0] nl_operator_4_false_3_acc_nl;
  wire[10:0] operator_10_false_acc_nl;
  wire[11:0] nl_operator_10_false_acc_nl;
  wire[3:0] operator_4_false_acc_nl;
  wire[4:0] nl_operator_4_false_acc_nl;
  wire VCOL_VCOL_nor_7_nl;
  wire VCOL_and_72_nl;
  wire or_367_nl;
  wire mux_266_nl;
  wire nor_106_nl;
  wire mux_265_nl;
  wire or_365_nl;
  wire nand_61_nl;
  wire mux_267_nl;
  wire and_257_nl;
  wire or_453_nl;
  wire VCOL_VCOL_and_3_nl;
  wire[7:0] VCOL_VCOL_and_4_nl;
  wire[1:0] VCOL_VCOL_and_5_nl;
  wire VCOL_VCOL_and_6_nl;
  wire VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_4_nl;
  wire[6:0] VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_5_nl;
  wire[9:0] operator_8_false_mul_nl;
  wire[10:0] nl_operator_8_false_mul_nl;
  wire[2:0] VCOL_else_5_if_for_mux_90_nl;
  wire VCOL_else_5_if_for_nand_14_nl;
  wire VCOL_else_5_if_for_and_70_nl;
  wire VCOL_else_5_if_for_and_67_nl;
  wire nand_55_nl;
  wire VCOL_else_5_if_for_nand_8_nl;
  wire VCOL_else_5_if_for_and_56_nl;
  wire VCOL_else_5_if_for_and_58_nl;
  wire VCOL_else_5_if_for_nand_6_nl;
  wire VCOL_else_5_if_for_or_7_nl;
  wire VCOL_else_4_and_13_nl;
  wire[7:0] tmp_pix_mux_7_nl;
  wire[7:0] tmp_pix_mux_11_nl;
  wire[7:0] tmp_pix_mux_14_nl;
  wire[8:0] operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_nl;
  wire[9:0] nl_operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_nl;
  wire VCOL_else_5_if_for_and_46_nl;
  wire mux_218_nl;
  wire mux_217_nl;
  wire mux_234_nl;
  wire mux_241_nl;
  wire mux_240_nl;
  wire mux_238_nl;
  wire mux_237_nl;
  wire or_334_nl;
  wire mux_246_nl;
  wire mux_245_nl;
  wire nor_119_nl;
  wire mux_244_nl;
  wire or_342_nl;
  wire[2:0] operator_4_false_2_acc_nl;
  wire[3:0] nl_operator_4_false_2_acc_nl;
  wire[1:0] operator_4_false_mux_nl;
  wire operator_4_false_mux_2_nl;
  wire[11:0] operator_11_false_acc_nl;
  wire[12:0] nl_operator_11_false_acc_nl;
  wire VCOL_if_3_not_nl;
  wire[7:0] VCOL_else_5_if_for_mux_80_nl;
  wire[7:0] VCOL_else_5_if_for_mux_79_nl;
  wire mux_260_nl;
  wire mux_259_nl;
  wire and_255_nl;
  wire mux_258_nl;
  wire or_359_nl;
  wire[7:0] VCOL_mux_40_nl;
  wire[7:0] VCOL_else_5_if_for_mux_78_nl;
  wire mux_257_nl;
  wire nor_123_nl;
  wire nor_124_nl;
  wire or_463_nl;
  wire j_mux1h_2_nl;
  wire mux_509_nl;
  wire mux_508_nl;
  wire mux_507_nl;
  wire nor_283_nl;
  wire or_767_nl;
  wire mux_506_nl;
  wire nor_285_nl;
  wire mux_300_nl;
  wire nor_286_nl;
  wire nor_287_nl;
  wire or_517_nl;
  wire mux_301_nl;
  wire or_516_nl;
  wire or_529_nl;
  wire mux_311_nl;
  wire or_528_nl;
  wire nand_69_nl;
  wire or_544_nl;
  wire or_542_nl;
  wire or_556_nl;
  wire or_578_nl;
  wire mux_369_nl;
  wire and_456_nl;
  wire mux_375_nl;
  wire nor_297_nl;
  wire or_599_nl;
  wire mux_380_nl;
  wire mux_379_nl;
  wire mux_378_nl;
  wire or_608_nl;
  wire or_789_nl;
  wire mux_377_nl;
  wire or_790_nl;
  wire or_605_nl;
  wire mux_390_nl;
  wire nor_302_nl;
  wire or_615_nl;
  wire mux_395_nl;
  wire mux_394_nl;
  wire mux_393_nl;
  wire or_624_nl;
  wire or_792_nl;
  wire mux_392_nl;
  wire or_793_nl;
  wire or_621_nl;
  wire nor_306_nl;
  wire or_633_nl;
  wire or_632_nl;
  wire mux_409_nl;
  wire mux_408_nl;
  wire mux_407_nl;
  wire or_641_nl;
  wire or_639_nl;
  wire mux_406_nl;
  wire or_794_nl;
  wire or_795_nl;
  wire nor_312_nl;
  wire or_651_nl;
  wire or_650_nl;
  wire mux_423_nl;
  wire mux_422_nl;
  wire mux_421_nl;
  wire or_659_nl;
  wire or_657_nl;
  wire mux_420_nl;
  wire or_797_nl;
  wire or_798_nl;
  wire or_670_nl;
  wire mux_433_nl;
  wire or_668_nl;
  wire or_666_nl;
  wire mux_447_nl;
  wire nor_316_nl;
  wire and_459_nl;
  wire mux_452_nl;
  wire mux_451_nl;
  wire mux_450_nl;
  wire or_693_nl;
  wire or_692_nl;
  wire mux_449_nl;
  wire or_799_nl;
  wire or_690_nl;
  wire nor_318_nl;
  wire or_702_nl;
  wire or_701_nl;
  wire mux_466_nl;
  wire mux_465_nl;
  wire mux_464_nl;
  wire or_709_nl;
  wire or_800_nl;
  wire mux_463_nl;
  wire or_801_nl;
  wire or_802_nl;
  wire nor_325_nl;
  wire or_717_nl;
  wire or_715_nl;
  wire mux_473_nl;
  wire or_725_nl;
  wire or_722_nl;
  wire nor_329_nl;
  wire or_735_nl;
  wire or_734_nl;
  wire mux_488_nl;
  wire mux_487_nl;
  wire mux_486_nl;
  wire or_743_nl;
  wire or_805_nl;
  wire mux_485_nl;
  wire or_806_nl;
  wire or_807_nl;
  wire nor_334_nl;
  wire and_465_nl;
  wire[9:0] VROW_VROW_mux_1_nl;
  wire VROW_or_2_nl;

  // Interconnect Declarations for Component Instantiations 
  wire  nl_EdgeDetect_IP_Denoise_IP_run_run_fsm_inst_VCOL_C_0_tr0;
  assign nl_EdgeDetect_IP_Denoise_IP_run_run_fsm_inst_VCOL_C_0_tr0 = ~(VCOL_stage_0_1
      | VCOL_stage_0_2);
  EdgeDetect_IP_Denoise_IP_run_dat_in_rsci EdgeDetect_IP_Denoise_IP_run_dat_in_rsci_inst
      (
      .dat_in_rsc_dat(dat_in_rsc_dat),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy),
      .run_wen(run_wen),
      .dat_in_rsci_oswt(reg_dat_in_rsci_iswt0_cse),
      .dat_in_rsci_wen_comp(dat_in_rsci_wen_comp),
      .dat_in_rsci_idat_mxwt(dat_in_rsci_idat_mxwt)
    );
  EdgeDetect_IP_Denoise_IP_run_dat_out_rsci EdgeDetect_IP_Denoise_IP_run_dat_out_rsci_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_out_rsc_dat(dat_out_rsc_dat),
      .dat_out_rsc_vld(dat_out_rsc_vld),
      .dat_out_rsc_rdy(dat_out_rsc_rdy),
      .run_wen(run_wen),
      .dat_out_rsci_oswt(reg_dat_out_rsci_iswt0_cse),
      .dat_out_rsci_wen_comp(dat_out_rsci_wen_comp),
      .dat_out_rsci_idat(dat_out_rsci_idat)
    );
  EdgeDetect_IP_Denoise_IP_run_wait_dp EdgeDetect_IP_Denoise_IP_run_wait_dp_inst
      (
      .line_buf0_rsci_en_d(line_buf0_rsci_en_d),
      .line_buf1_rsci_en_d(line_buf1_rsci_en_d),
      .run_wen(run_wen),
      .line_buf0_rsci_cgo(reg_line_buf0_rsci_cgo_ir_cse),
      .line_buf0_rsci_cgo_ir_unreg(and_133_rmff),
      .line_buf1_rsci_cgo(reg_line_buf1_rsci_cgo_ir_cse),
      .line_buf1_rsci_cgo_ir_unreg(and_131_rmff)
    );
  EdgeDetect_IP_Denoise_IP_run_ctrl_signal_triosy_obj EdgeDetect_IP_Denoise_IP_run_ctrl_signal_triosy_obj_inst
      (
      .ctrl_signal_triosy_lz(ctrl_signal_triosy_lz),
      .run_wten(run_wten),
      .ctrl_signal_triosy_obj_iswt0(ctrl_signal_triosy_obj_iswt0)
    );
  EdgeDetect_IP_Denoise_IP_run_staller EdgeDetect_IP_Denoise_IP_run_staller_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .run_wten(run_wten),
      .dat_in_rsci_wen_comp(dat_in_rsci_wen_comp),
      .dat_out_rsci_wen_comp(dat_out_rsci_wen_comp)
    );
  EdgeDetect_IP_Denoise_IP_run_run_fsm EdgeDetect_IP_Denoise_IP_run_run_fsm_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .fsm_output(fsm_output),
      .VCOL_C_0_tr0(nl_EdgeDetect_IP_Denoise_IP_run_run_fsm_inst_VCOL_C_0_tr0),
      .VROW_C_0_tr0(VROW_equal_tmp)
    );
  assign VROW_y_or_cse = (fsm_output[0]) | (fsm_output[2]);
  assign nor_238_cse = ~(operator_4_false_3_acc_itm_4 | operator_4_false_2_acc_itm_2
      | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1));
  assign nor_nl = ~((~ lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) | exitL_exitL_exit_VCOL_else_5_if_for_1_sva
      | operator_4_false_acc_itm_3);
  assign nand_100_nl = ~(operator_4_false_acc_itm_3 & (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]));
  assign or_772_nl = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]) | nor_238_cse;
  assign mux_272_nl = MUX_s_1_2_2(nand_100_nl, or_772_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign nor_239_nl = ~((ctrl_signal_rsci_idat[1]) | (~ operator_4_false_acc_itm_3));
  assign mux_nl = MUX_s_1_2_2((ctrl_signal_rsci_idat[1]), nor_239_nl, ctrl_signal_rsci_idat[0]);
  assign nor_240_nl = ~(VCOL_else_4_else_aif_equal_tmp | mux_nl);
  assign mux_273_nl = MUX_s_1_2_2(mux_272_nl, nor_240_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_274_nl = MUX_s_1_2_2(nor_nl, mux_273_nl, VCOL_stage_0_2);
  assign and_272_cse = mux_274_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_1;
  assign nand_56_nl = ~((ctrl_signal_rsci_idat[0]) & operator_4_false_acc_itm_3);
  assign mux_231_cse = MUX_s_1_2_2(nand_56_nl, (ctrl_signal_rsci_idat[0]), ctrl_signal_rsci_idat[1]);
  assign or_479_cse = (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0
      | operator_4_false_2_acc_itm_2 | operator_4_false_3_acc_itm_4;
  assign operator_10_false_1_and_cse = run_wen & VCOL_aelse_VCOL_aelse_and_cse;
  assign operator_11_false_6_and_cse = run_wen & (~ mux_tmp_8) & VCOL_stage_0_1;
  assign or_774_cse = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10);
  assign or_775_cse = VCOL_else_4_else_aif_equal_tmp | (ctrl_signal_rsci_idat!=2'b10);
  assign mux_284_nl = MUX_s_1_2_2(or_774_cse, or_775_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign and_281_cse = (~(mux_284_nl & VCOL_stage_0_2)) & and_dcpl_66;
  assign or_72_cse = (~ lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) | exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign VCOL_if_6_VCOL_if_6_or_cse = (VROW_y_sva!=10'b0000000000);
  assign nor_85_cse = ~(VCOL_else_4_else_aif_equal_tmp | (~ mux_231_cse));
  assign or_325_cse = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) | (~ operator_4_false_acc_itm_3);
  assign VCOL_and_46_tmp = (~ operator_4_false_3_acc_itm_4) & VCOL_else_5_if_for_equal_tmp_mx0w1
      & VCOL_equal_tmp_7;
  assign j_and_1_rgt = (~ VCOL_and_46_tmp) & j_2_0_lpi_3_dfm_3_1_mx1c0;
  assign nor_115_nl = ~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva | (~ lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3)
      | (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0
      | (~ exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3));
  assign nor_116_nl = ~(exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 | (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1)
      | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | (~ exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1)
      | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10));
  assign mux_242_cse = MUX_s_1_2_2(nor_115_nl, nor_116_nl, VCOL_stage_0_2);
  assign j_or_1_itm = (VCOL_and_46_tmp & j_2_0_lpi_3_dfm_3_1_mx1c0) | (mux_242_cse
      & operator_4_false_3_acc_itm_4 & VCOL_stage_0_1);
  assign or_495_cse = (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0;
  assign and_71_nl = VCOL_stage_0_2 & nor_tmp_55;
  assign and_253_nl = (VCOL_x_sva[0]) & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign or_452_nl = (~((~ VCOL_else_5_if_for_mux_78_tmp_0) | (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1)
      | VCOL_else_4_else_aif_equal_tmp)) | nor_tmp_55;
  assign mux_252_nl = MUX_s_1_2_2(and_253_nl, or_452_nl, VCOL_stage_0_2);
  assign nand_15_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0 &
      (~ nor_tmp_55));
  assign mux_251_nl = MUX_s_1_2_2(exitL_exitL_exit_VCOL_else_5_if_for_1_sva, nand_15_nl,
      VCOL_stage_0_2);
  assign or_347_nl = (VROW_y_sva!=10'b0000000000) | operator_11_false_4_operator_11_false_4_nor_tmp;
  assign mux_253_nl = MUX_s_1_2_2(mux_252_nl, mux_251_nl, or_347_nl);
  assign mux_254_nl = MUX_s_1_2_2(and_71_nl, mux_253_nl, VCOL_stage_0_1);
  assign and_131_rmff = mux_254_nl & (fsm_output[1]);
  assign and_254_nl = exitL_exitL_exit_VCOL_else_5_if_for_1_sva & VCOL_stage_0_1;
  assign or_352_nl = exitL_exitL_exit_VCOL_else_5_if_for_1_sva | (~((~ VCOL_stage_0_1)
      | (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) | VCOL_else_4_else_aif_equal_tmp));
  assign mux_255_nl = MUX_s_1_2_2(and_254_nl, or_352_nl, VCOL_stage_0_2);
  assign and_133_rmff = mux_255_nl & (fsm_output[1]);
  assign mux_256_cse = MUX_s_1_2_2(exitL_exitL_exit_VCOL_else_5_if_for_1_sva, (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0), VCOL_stage_0_2);
  assign or_500_cse = VCOL_else_4_else_aif_equal_tmp | (~ VCOL_stage_0_1);
  assign VCOL_and_79_cse = run_wen & (~(or_dcpl_40 | (~ (fsm_output[1]))));
  assign or_501_cse = (VCOL_x_sva!=11'b00000000001);
  assign and_396_cse = VCOL_else_4_else_aif_equal_tmp & VROW_equal_tmp;
  assign and_397_cse = operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 &
      VCOL_else_4_else_aif_equal_tmp;
  assign nand_110_cse = ~(reg_operator_11_false_6_nor_itm_1_cse & (VCOL_x_sva[0]));
  assign nand_112_cse = ~(exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 & VCOL_stage_0_1);
  assign VCOL_else_5_if_for_and_6_cse = operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign mux_12_nl = MUX_s_1_2_2(or_tmp_20, lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0,
      VCOL_else_5_if_for_mux_78_tmp_0);
  assign mux_15_nl = MUX_s_1_2_2(or_tmp_20, mux_12_nl, operator_11_false_1_nor_tmp);
  assign rdbuf1_pix_and_1_cse = run_wen & (((VCOL_x_sva[0]) & (~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1)
      & exitL_exitL_exit_VCOL_else_5_if_for_1_sva) | VCOL_else_5_if_for_and_6_cse)
      & VCOL_stage_0_2 & (fsm_output[1]) & (mux_15_nl | (~ VCOL_stage_0_1));
  assign nand_114_cse = ~(lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1 & VCOL_stage_0_1);
  assign nand_116_cse = ~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) &
      VCOL_stage_0_1);
  assign or_522_cse = (VCOL_x_sva[10:1]!=10'b0000000000);
  assign or_521_nl = (ctrl_signal_rsci_idat[0]) | (~ VCOL_stage_0_1) | VCOL_else_4_else_aif_equal_tmp;
  assign or_520_nl = (~ (ctrl_signal_rsci_idat[0])) | (~ VCOL_stage_0_1) | VCOL_else_4_else_aif_equal_tmp;
  assign mux_306_nl = MUX_s_1_2_2(or_521_nl, or_520_nl, ctrl_signal_rsci_idat[1]);
  assign nor_150_nl = ~((VROW_y_sva!=10'b0000000001) | (VCOL_x_sva_2!=11'b00000000001));
  assign mux_307_cse = MUX_s_1_2_2(mux_306_nl, or_500_cse, nor_150_nl);
  assign or_564_cse = (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) | operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1;
  assign and_429_cse = (VCOL_x_sva[0]) & reg_operator_11_false_6_nor_itm_1_cse;
  assign and_431_cse = (VCOL_x_sva[0]) & VROW_equal_tmp & reg_operator_11_false_6_nor_itm_1_cse;
  assign nor_67_nl = ~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b00));
  assign nor_68_nl = ~(VCOL_else_4_else_aif_equal_tmp | (ctrl_signal_rsci_idat!=2'b00));
  assign mux_32_nl = MUX_s_1_2_2(nor_67_nl, nor_68_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign pix_result_and_cse = run_wen & VCOL_stage_0_2 & (fsm_output[1]) & (~(mux_32_nl
      & VCOL_stage_0_1));
  assign mux_36_cse = MUX_s_1_2_2((~ (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0])),
      (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]), VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign or_587_cse = ((ctrl_signal_rsci_idat==2'b11)) | VCOL_else_4_else_aif_equal_tmp;
  assign nor_16_cse = ~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva | (~ lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3));
  assign nor_270_cse = ~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva | (~ lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3)
      | (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0);
  assign or_593_cse = (~ operator_4_false_2_acc_itm_2) | operator_4_false_3_acc_itm_4;
  assign nor_271_nl = ~(exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 | (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1)
      | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10));
  assign mux_372_cse = MUX_s_1_2_2(nor_270_cse, nor_271_nl, VCOL_stage_0_2);
  assign or_612_cse = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10) |
      exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  assign nor_187_cse = ~(VCOL_else_4_else_aif_equal_tmp | (ctrl_signal_rsci_idat!=2'b10)
      | (~ operator_4_false_acc_itm_3));
  assign nor_186_cse = ~((~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) | VCOL_else_4_else_aif_equal_tmp
      | (ctrl_signal_rsci_idat!=2'b10) | (~ operator_4_false_acc_itm_3));
  assign nor_272_cse = ~((i_1_lpi_3_dfm_1_1[3:2]!=2'b00));
  assign nor_196_cse = ~((i_1_lpi_3_dfm_1_1[3:2]!=2'b01));
  assign nor_211_cse = ~((max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b01) | (~ max_i_2_0_lpi_3_dfm_1_1_0));
  assign nand_142_cse = ~(VCOL_stage_0_2 & VCOL_else_4_else_aif_equal_tmp & exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign and_439_nl = (~(VCOL_else_4_else_aif_equal_tmp & exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1))
      & exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1;
  assign mux_502_nl = MUX_s_1_2_2(exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3,
      and_439_nl, VCOL_stage_0_2);
  assign mux_503_nl = MUX_s_1_2_2(mux_502_nl, nand_142_cse, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign and_384_cse = mux_503_nl & and_dcpl_66;
  assign VCOL_x_and_cse = exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 & VCOL_stage_0_2;
  assign VCOL_x_sva_mx1 = MUX_v_11_2_2(VCOL_x_sva, VCOL_x_sva_2, VCOL_x_and_cse);
  assign lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1_mx1 = MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1,
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1, VCOL_stage_0_2);
  assign lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0_mx1 = MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0,
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0, VCOL_stage_0_2);
  assign lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0 = VCOL_else_4_else_aif_equal_tmp
      | (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign VCOL_else_5_if_for_equal_tmp_mx0w1 = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1_mx1
      & lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_mx0w0 & (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_0_mx0w1);
  assign VCOL_aelse_VCOL_aelse_and_cse = VCOL_stage_0_1 & nand_142_cse;
  assign VCOL_else_5_else_if_for_VCOL_else_5_else_if_for_or_nl = exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1
      | (~ operator_4_false_acc_itm_3);
  assign VCOL_else_5_if_for_mux_68_mx0w0 = MUX_s_1_2_2(VCOL_else_5_else_if_for_VCOL_else_5_else_if_for_or_nl,
      (~ operator_4_false_3_acc_itm_4), VCOL_else_5_if_for_equal_tmp_mx0w1);
  assign exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1 = MUX_s_1_2_2(exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3,
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1, VCOL_stage_0_2);
  assign operator_10_false_1_operator_10_false_1_and_cse_sva_1 = (VROW_y_sva==10'b0000000001);
  assign operator_11_false_1_nor_tmp = ~((VCOL_x_sva_mx1[10:1]!=10'b0000000000));
  assign mux_216_nl = MUX_s_1_2_2(or_72_cse, or_612_cse, VCOL_stage_0_2);
  assign and_217_m1c = (~ mux_216_nl) & VCOL_stage_0_1 & (fsm_output[1]);
  assign max_i_or_m1c = ((~ VCOL_else_5_if_for_equal_tmp_mx0w1) & and_217_m1c) |
      (and_dcpl_25 & (fsm_output[1]));
  assign max_i_or_nl = (~ (fsm_output[1])) | or_dcpl_4 | ((~ VCOL_stage_0_2) & max_i_or_m1c);
  assign max_i_and_2_nl = VCOL_stage_0_2 & max_i_or_m1c;
  assign max_i_and_1_nl = VCOL_else_5_if_for_equal_tmp_mx0w1 & and_217_m1c;
  assign j_2_0_lpi_3_dfm_3_1_mx0w0_0 = MUX1HOT_s_1_3_2(j_2_0_lpi_3_dfm_3_1_rsp_1,
      max_i_3_lpi_3_dfm_3_1, max_i_3_lpi_3_dfm_1_1_mx0, {max_i_or_nl , max_i_and_2_nl
      , max_i_and_1_nl});
  assign nl_i_1_sva_1_mx0w0 = i_1_lpi_3_dfm_2 + 4'b0001;
  assign i_1_sva_1_mx0w0 = nl_i_1_sva_1_mx0w0[3:0];
  assign nl_i_sva_2 = ({i_lpi_3_dfm_mx0_3 , i_lpi_3_dfm_mx0_2_0}) + 4'b0001;
  assign i_sva_2 = nl_i_sva_2[3:0];
  assign mux_250_nl = MUX_s_1_2_2(or_72_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1,
      VCOL_stage_0_2);
  assign VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1_mx0 = MUX_v_2_2_2(VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1,
      ctrl_signal_rsci_idat, mux_250_nl);
  assign nor_126_nl = ~((VCOL_x_sva[0]) | (~ exitL_exitL_exit_VCOL_else_5_if_for_1_sva));
  assign nor_127_nl = ~(VCOL_else_5_if_for_mux_78_tmp_0 | (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1)
      | VCOL_else_4_else_aif_equal_tmp);
  assign mux_262_cse = MUX_s_1_2_2(nor_126_nl, nor_127_nl, VCOL_stage_0_2);
  assign VCOL_else_5_if_for_and_44_nl = (~ operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1)
      & exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  assign VCOL_else_5_if_for_and_48_nl = operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1
      & exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  assign VCOL_VCOL_slc_pix_39_32_2_lpi_3_dfm_mx1w0 = MUX1HOT_v_8_3_2(VCOL_VCOL_slc_pix_39_32_2_lpi_4,
      pix_1_lpi_3_dfm_10_mx1w0, pix_4_lpi_3_dfm_1_mx0, {(~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1)
      , VCOL_else_5_if_for_and_44_nl , VCOL_else_5_if_for_and_48_nl});
  assign VCOL_else_5_if_for_or_9_nl = (~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva
      & (~((~ VCOL_land_lpi_3_dfm_1) & VCOL_else_5_if_for_and_49_cse_1)))) | ((~
      VCOL_land_lpi_3_dfm_1) & VCOL_else_4_else_else_or_6_m1c_1 & VCOL_else_5_if_for_and_50_m1c_1);
  assign VCOL_else_5_if_for_or_10_nl = (VCOL_land_lpi_3_dfm_1 & VCOL_else_4_else_else_or_6_m1c_1
      & VCOL_else_5_if_for_and_50_m1c_1) | (VCOL_land_lpi_3_dfm_1 & VCOL_else_5_if_for_and_49_cse_1);
  assign VCOL_else_5_if_for_or_11_nl = (VCOL_else_4_else_aif_equal_tmp & VCOL_else_4_else_else_and_3_m1c_1
      & VCOL_else_5_if_for_and_50_m1c_1) | (and_397_cse & (~ and_431_cse) & VCOL_else_5_if_for_and_9_m1c_1);
  assign VCOL_else_5_if_for_or_12_nl = (VROW_equal_tmp & VCOL_else_4_else_else_and_3_m1c_1
      & VCOL_else_5_if_for_and_50_m1c_1) | VCOL_else_5_if_for_and_51_cse_1;
  assign VCOL_else_5_if_for_and_65_nl = and_396_cse & VCOL_else_5_if_for_and_50_m1c_1;
  assign pix_2_lpi_3_dfm_9_mx1w0 = MUX1HOT_v_8_5_2(pix_2_lpi_3, dat_in_rsci_idat_mxwt,
      pix_5_lpi_3, pix_1_lpi_3_dfm_11, pix_4_lpi_3_dfm_mx0, {VCOL_else_5_if_for_or_9_nl
      , VCOL_else_5_if_for_or_10_nl , VCOL_else_5_if_for_or_11_nl , VCOL_else_5_if_for_or_12_nl
      , VCOL_else_5_if_for_and_65_nl});
  assign VCOL_else_5_if_for_nand_12_nl = ~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva
      & (~(VCOL_lor_lpi_3_dfm_1 & (~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1)
      & VCOL_else_5_if_for_or_m1c_1)));
  assign VCOL_else_5_if_for_and_61_nl = (~((VCOL_x_sva[0]) | VCOL_lor_lpi_3_dfm_1
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1)) & VCOL_else_5_if_for_or_m1c_1;
  assign VCOL_and_35_nl = (VCOL_x_sva[0]) & (~ VCOL_lor_lpi_3_dfm_1) & (~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1)
      & VCOL_else_5_if_for_or_m1c_1;
  assign VCOL_else_5_if_for_and_62_nl = operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      & VCOL_else_5_if_for_or_m1c_1;
  assign VCOL_else_5_if_for_and_53_nl = ((VCOL_else_4_else_aif_equal_tmp & (~ operator_10_false_1_operator_10_false_1_and_cse_sva_1_1)
      & VCOL_else_4_else_else_else_and_tmp_1) | and_396_cse) & VCOL_and_m1c_1;
  assign VCOL_else_5_if_for_or_6_nl = (operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & VCOL_else_4_else_else_else_and_tmp_1 & VCOL_and_m1c_1) | VCOL_else_5_if_for_and_49_cse_1;
  assign VCOL_and_38_nl = and_397_cse & VCOL_VCOL_nor_1_m1c_1 & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign pix_0_lpi_3_dfm_10_mx1w0 = MUX1HOT_v_8_7_2(pix_0_lpi_3, (rdbuf1_pix_lpi_3[7:0]),
      (rdbuf1_pix_lpi_3[15:8]), (line_buf1_rsci_q_d[15:8]), pix_3_lpi_3_dfm_mx0,
      pix_1_lpi_3_dfm_11, pix_4_lpi_3_dfm_mx0, {VCOL_else_5_if_for_nand_12_nl , VCOL_else_5_if_for_and_61_nl
      , VCOL_and_35_nl , VCOL_else_5_if_for_and_62_nl , VCOL_else_5_if_for_and_53_nl
      , VCOL_else_5_if_for_or_6_nl , VCOL_and_38_nl});
  assign operator_11_false_4_operator_11_false_4_nor_tmp = ~((VCOL_x_sva_mx1!=11'b00000000000));
  assign VCOL_else_5_if_for_and_63_nl = (~ VCOL_or_7_tmp_1) & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign VCOL_else_5_if_for_and_64_nl = VCOL_or_7_tmp_1 & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign pix_1_lpi_3_dfm_10_mx1w0 = MUX1HOT_v_8_3_2(pix_1_lpi_3, pix_1_lpi_3_dfm_11,
      pix_4_lpi_3_dfm_mx0, {(~ exitL_exitL_exit_VCOL_else_5_if_for_1_sva) , VCOL_else_5_if_for_and_63_nl
      , VCOL_else_5_if_for_and_64_nl});
  assign VCOL_VCOL_oelse_operator_11_false_or_tmp = (VCOL_x_sva_mx1!=11'b00000000000);
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_3_nl = (VCOL_else_5_if_for_acc_psp_sva_1[12:11]!=2'b00);
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_and_3_nl = pix_result_11_lpi_3 & (~
      exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1);
  assign VCOL_mux1h_20_nl = MUX1HOT_s_1_3_2(VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_3_nl,
      pix_result_11_lpi_3, VCOL_else_5_if_for_VCOL_else_5_if_for_and_3_nl, {VCOL_equal_tmp_1_1
      , VCOL_or_1_cse_1 , VCOL_and_6_m1c_1});
  assign pix_result_11_lpi_3_dfm_3_mx1w0 = VCOL_mux1h_20_nl & (~ VCOL_equal_tmp_1);
  assign VCOL_else_5_if_for_mux_73_nl = MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3,
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0, VCOL_stage_0_2);
  assign lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_mx0w0 = VCOL_else_5_if_for_mux_73_nl
      & (~ mux_256_cse);
  assign lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_0_mx0w1 = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0_mx1
      & lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_mx0w0;
  assign VCOL_and_42_cse = exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1 & VCOL_and_6_m1c_1;
  assign VCOL_and_41_cse = (~ exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1) & VCOL_and_6_m1c_1;
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_1_nl = MUX_v_8_2_2((VCOL_else_5_if_for_acc_psp_sva_1[10:3]),
      8'b11111111, (VCOL_else_5_if_for_acc_psp_sva_1[12]));
  assign VCOL_or_2_nl = VCOL_and_16_cse_1 | VCOL_equal_tmp_3_1 | VCOL_and_41_cse;
  assign pix_result_10_3_lpi_3_dfm_3_mx1w0 = MUX1HOT_v_8_4_2(pix_4_lpi_3_dfm_1_mx0,
      VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_1_nl, pix_result_10_3_lpi_3,
      reg_max_val_10_3_lpi_3_dfm_1_1_cse, {VCOL_equal_tmp_1 , VCOL_equal_tmp_1_1
      , VCOL_or_2_nl , VCOL_and_42_cse});
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_nl = (VCOL_else_5_if_for_acc_psp_sva_1[2:1])
      | (signext_2_1(VCOL_else_5_if_for_acc_psp_sva_1[12])) | ({{1{VCOL_and_6_m1c_1}},
      VCOL_and_6_m1c_1});
  assign nor_133_nl = ~((~(VCOL_and_41_cse | VCOL_or_1_cse_1)) | VCOL_equal_tmp_1);
  assign mux_270_nl = MUX_v_2_2_2(VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_nl,
      pix_result_2_1_lpi_3, nor_133_nl);
  assign nor_135_nl = ~(VCOL_and_42_cse | VCOL_equal_tmp_1);
  assign pix_result_2_1_lpi_3_dfm_3_mx1w0 = MUX_v_2_2_2(2'b00, mux_270_nl, nor_135_nl);
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_2_nl = (VCOL_else_5_if_for_acc_psp_sva_1[0])
      | (VCOL_else_5_if_for_acc_psp_sva_1[12]);
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_and_5_nl = pix_result_0_lpi_3 & (~
      exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1);
  assign VCOL_mux1h_23_nl = MUX1HOT_s_1_3_2(VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_2_nl,
      pix_result_0_lpi_3, VCOL_else_5_if_for_VCOL_else_5_if_for_and_5_nl, {VCOL_equal_tmp_1_1
      , VCOL_or_1_cse_1 , VCOL_and_6_m1c_1});
  assign pix_result_0_lpi_3_dfm_3_mx1w0 = VCOL_mux1h_23_nl & (~ VCOL_equal_tmp_1);
  assign i_1_lpi_3_dfm_2 = MUX_v_4_2_2(4'b0000, i_1_lpi_3_dfm_1_1, lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_mx0w0);
  assign exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_2 = ~(operator_4_false_2_acc_itm_2
      | operator_4_false_3_acc_itm_4);
  assign VCOL_equal_tmp_5 = ~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1_mx0!=2'b00));
  assign VCOL_equal_tmp_6 = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1_mx0==2'b11);
  assign VCOL_equal_tmp_7 = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1_mx0==2'b10);
  assign tmp_pix_1_lpi_3_mx1 = MUX_v_8_2_2(tmp_pix_1_lpi_3, tmp_pix_1_lpi_3_dfm_2_mx2w1,
      VCOL_stage_0_2);
  assign VCOL_or_11_nl = (~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_17_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_1_tmp_1)
      & VCOL_and_6_m1c_1);
  assign VCOL_else_5_if_for_and_18_nl = VCOL_else_5_else_if_for_and_17_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_and_54_nl = VCOL_else_5_else_if_for_1_for_and_1_tmp_1 & VCOL_and_6_m1c_1;
  assign tmp_pix_1_lpi_3_dfm_2_mx2w1 = MUX1HOT_v_8_3_2(tmp_pix_1_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {VCOL_or_11_nl
      , VCOL_else_5_if_for_and_18_nl , VCOL_and_54_nl});
  assign tmp_pix_5_lpi_3_mx1 = MUX_v_8_2_2(tmp_pix_5_lpi_3, tmp_pix_5_lpi_3_dfm_2_mx2w1,
      VCOL_stage_0_2);
  assign VCOL_or_15_nl = (~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_14_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_5_tmp_1)
      & VCOL_and_6_m1c_1);
  assign VCOL_else_5_if_for_and_26_nl = VCOL_else_5_else_if_for_and_14_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_and_62_nl = VCOL_else_5_else_if_for_1_for_and_5_tmp_1 & VCOL_and_6_m1c_1;
  assign tmp_pix_5_lpi_3_dfm_2_mx2w1 = MUX1HOT_v_8_3_2(tmp_pix_5_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {VCOL_or_15_nl
      , VCOL_else_5_if_for_and_26_nl , VCOL_and_62_nl});
  assign tmp_pix_2_lpi_3_mx1 = MUX_v_8_2_2(tmp_pix_2_lpi_3, tmp_pix_2_lpi_3_dfm_2_mx2w1,
      VCOL_stage_0_2);
  assign VCOL_or_12_nl = (~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_15_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_2_tmp_1)
      & VCOL_and_6_m1c_1);
  assign VCOL_else_5_if_for_and_20_nl = VCOL_else_5_else_if_for_and_15_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_and_56_nl = VCOL_else_5_else_if_for_1_for_and_2_tmp_1 & VCOL_and_6_m1c_1;
  assign tmp_pix_2_lpi_3_dfm_2_mx2w1 = MUX1HOT_v_8_3_2(tmp_pix_2_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {VCOL_or_12_nl
      , VCOL_else_5_if_for_and_20_nl , VCOL_and_56_nl});
  assign VCOL_or_16_nl = (~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_16_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_6_tmp_1)
      & VCOL_and_6_m1c_1);
  assign VCOL_else_5_if_for_and_28_nl = VCOL_else_5_else_if_for_and_16_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_and_64_nl = VCOL_else_5_else_if_for_1_for_and_6_tmp_1 & VCOL_and_6_m1c_1;
  assign tmp_pix_6_lpi_3_dfm_2_mx2w1 = MUX1HOT_v_8_3_2(tmp_pix_6_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {VCOL_or_16_nl
      , VCOL_else_5_if_for_and_28_nl , VCOL_and_64_nl});
  assign tmp_pix_3_lpi_3_mx1 = MUX_v_8_2_2(tmp_pix_3_lpi_3, tmp_pix_3_lpi_3_dfm_2_mx2w1,
      VCOL_stage_0_2);
  assign VCOL_or_13_nl = (~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_13_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_3_tmp_1)
      & VCOL_and_6_m1c_1);
  assign VCOL_else_5_if_for_and_22_nl = VCOL_else_5_else_if_for_and_13_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_and_58_nl = VCOL_else_5_else_if_for_1_for_and_3_tmp_1 & VCOL_and_6_m1c_1;
  assign tmp_pix_3_lpi_3_dfm_2_mx2w1 = MUX1HOT_v_8_3_2(tmp_pix_3_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {VCOL_or_13_nl
      , VCOL_else_5_if_for_and_22_nl , VCOL_and_58_nl});
  assign VCOL_or_17_nl = (~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_18_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_7_tmp_1)
      & VCOL_and_6_m1c_1);
  assign VCOL_else_5_if_for_and_30_nl = VCOL_else_5_else_if_for_and_18_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_and_66_nl = VCOL_else_5_else_if_for_1_for_and_7_tmp_1 & VCOL_and_6_m1c_1;
  assign tmp_pix_7_lpi_3_dfm_2_mx2w1 = MUX1HOT_v_8_3_2(tmp_pix_7_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {VCOL_or_17_nl
      , VCOL_else_5_if_for_and_30_nl , VCOL_and_66_nl});
  assign tmp_pix_nand_nl = ~(VCOL_stage_0_2 & (~((~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_19_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_tmp_1)
      & VCOL_and_6_m1c_1))));
  assign VCOL_else_5_if_for_and_16_nl = VCOL_else_5_else_if_for_and_19_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1 & VCOL_stage_0_2;
  assign VCOL_and_52_nl = VCOL_else_5_else_if_for_1_for_and_tmp_1 & VCOL_and_6_m1c_1
      & VCOL_stage_0_2;
  assign tmp_pix_0_lpi_3_mx0 = MUX1HOT_v_8_3_2(tmp_pix_0_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {tmp_pix_nand_nl
      , VCOL_else_5_if_for_and_16_nl , VCOL_and_52_nl});
  assign VCOL_or_18_nl = (~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_20_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_8_tmp_1)
      & VCOL_and_6_m1c_1);
  assign VCOL_else_5_if_for_and_32_nl = VCOL_else_5_else_if_for_and_20_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_and_68_nl = VCOL_else_5_else_if_for_1_for_and_8_tmp_1 & VCOL_and_6_m1c_1;
  assign tmp_pix_8_lpi_3_dfm_2_mx2w1 = MUX1HOT_v_8_3_2(tmp_pix_8_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {VCOL_or_18_nl
      , VCOL_else_5_if_for_and_32_nl , VCOL_and_68_nl});
  assign tmp_pix_4_lpi_3_mx1 = MUX_v_8_2_2(tmp_pix_4_lpi_3, tmp_pix_4_lpi_3_dfm_2_mx2w1,
      VCOL_stage_0_2);
  assign VCOL_or_14_nl = (~(VCOL_equal_tmp_2_1 & (VCOL_else_5_else_if_for_and_12_tmp_1
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3))) | ((~ VCOL_else_5_else_if_for_1_for_and_4_tmp_1)
      & VCOL_and_6_m1c_1);
  assign VCOL_else_5_if_for_and_24_nl = VCOL_else_5_else_if_for_and_12_tmp_1 & (~
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_and_60_nl = VCOL_else_5_else_if_for_1_for_and_4_tmp_1 & VCOL_and_6_m1c_1;
  assign tmp_pix_4_lpi_3_dfm_2_mx2w1 = MUX1HOT_v_8_3_2(tmp_pix_4_lpi_3, operator_8_false_mux_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1, {VCOL_or_14_nl
      , VCOL_else_5_if_for_and_24_nl , VCOL_and_60_nl});
  assign VCOL_else_5_else_if_for_1_for_VCOL_else_5_else_if_for_1_for_and_3_nl = max_i_3_lpi_3_mx1
      & (~ exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1);
  assign max_i_3_lpi_3_dfm_1_1_mx0 = MUX_s_1_2_2(VCOL_else_5_else_if_for_1_for_VCOL_else_5_else_if_for_1_for_and_3_nl,
      i_lpi_3_dfm_mx0_3, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign nl_operator_4_false_3_acc_nl = conv_u2s_4_5(i_sva_2) + 5'b10111;
  assign operator_4_false_3_acc_nl = nl_operator_4_false_3_acc_nl[4:0];
  assign operator_4_false_3_acc_itm_4 = readslicef_5_1_4(operator_4_false_3_acc_nl);
  assign max_i_3_lpi_3_mx1 = MUX_s_1_2_2(j_2_0_lpi_3_dfm_3_1_rsp_1, max_i_3_lpi_3_dfm_3_1,
      VCOL_stage_0_2);
  assign nl_operator_10_false_acc_nl = ({1'b1 , heightIn}) + conv_u2s_10_11(~ VROW_y_sva);
  assign operator_10_false_acc_nl = nl_operator_10_false_acc_nl[10:0];
  assign operator_10_false_acc_itm_10_1 = readslicef_11_1_10(operator_10_false_acc_nl);
  assign nl_operator_4_false_acc_nl = i_1_sva_1_mx0w0 + 4'b0111;
  assign operator_4_false_acc_nl = nl_operator_4_false_acc_nl[3:0];
  assign operator_4_false_acc_itm_3 = readslicef_4_1_3(operator_4_false_acc_nl);
  assign lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_3_1_1 = (~(exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_2
      | VCOL_else_5_if_for_and_14_ssc_1)) | (~(operator_4_false_acc_itm_3 | VCOL_else_5_if_for_equal_tmp_mx0w1));
  assign VCOL_else_5_if_for_and_14_ssc_1 = operator_4_false_acc_itm_3 & (~ VCOL_else_5_if_for_equal_tmp_mx0w1);
  assign i_lpi_3_dfm_mx0_3 = (i_lpi_3_dfm_2_1[3]) & (~ exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1);
  assign i_lpi_3_dfm_mx0_2_0 = MUX_v_3_2_2((i_lpi_3_dfm_2_1[2:0]), operator_4_false_acc_psp_sva_1,
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1);
  assign nl_operator_4_false_acc_psp_sva_1 = ({j_2_0_lpi_3_dfm_3_1_rsp_0 , j_2_0_lpi_3_dfm_3_1_rsp_1})
      + 3'b001;
  assign operator_4_false_acc_psp_sva_1 = nl_operator_4_false_acc_psp_sva_1[2:0];
  assign pix_3_lpi_3_dfm_mx0 = MUX_v_8_2_2(pix_3_lpi_3, (line_buf1_rsci_q_d[7:0]),
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign pix_4_lpi_3_dfm_mx0 = MUX_v_8_2_2(pix_4_lpi_3, (line_buf0_rsci_q_d[7:0]),
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign VCOL_VCOL_nor_7_nl = ~((VCOL_x_sva[0]) | reg_operator_11_false_6_nor_itm_1_cse
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign VCOL_and_72_nl = reg_operator_11_false_6_nor_itm_1_cse & (~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign pix_1_lpi_3_dfm_11 = MUX1HOT_v_8_4_2((rdbuf0_pix_lpi_3[7:0]), (rdbuf0_pix_lpi_3[15:8]),
      pix_1_lpi_3, (line_buf0_rsci_q_d[15:8]), {VCOL_VCOL_nor_7_nl , VCOL_and_37_itm_1
      , VCOL_and_72_nl , operator_11_false_4_operator_11_false_4_nor_cse_sva_1});
  assign or_365_nl = operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 | (~
      VCOL_else_4_else_aif_equal_tmp);
  assign mux_265_nl = MUX_s_1_2_2(and_397_cse, or_365_nl, VCOL_else_4_else_else_else_nor_1_tmp);
  assign nor_106_nl = ~(reg_operator_11_false_6_nor_itm_1_cse | (~ mux_265_nl));
  assign mux_266_nl = MUX_s_1_2_2(and_397_cse, nor_106_nl, VCOL_x_sva[0]);
  assign or_367_nl = mux_266_nl | (~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva &
      VROW_equal_tmp)) | VCOL_land_1_lpi_3_dfm_1;
  assign VCOL_else_5_if_for_mux_87_cse = MUX_v_8_2_2(pix_4_lpi_3_dfm_mx0, pix_5_lpi_3,
      or_367_nl);
  assign and_257_nl = VCOL_else_4_else_else_else_nor_1_tmp & (~ and_397_cse);
  assign or_453_nl = reg_operator_11_false_6_nor_itm_1_cse | (~((~ VCOL_else_4_else_else_else_nor_1_tmp)
      | VCOL_else_4_else_aif_equal_tmp));
  assign mux_267_nl = MUX_s_1_2_2(and_257_nl, or_453_nl, VROW_equal_tmp);
  assign nand_61_nl = ~(((mux_267_nl & (VCOL_x_sva[0])) | VCOL_land_1_lpi_3_dfm_1)
      & exitL_exitL_exit_VCOL_else_5_if_for_1_sva);
  assign pix_7_lpi_3_dfm_5_mx0 = MUX_v_8_2_2(pix_4_lpi_3_dfm_mx0, pix_7_lpi_3, nand_61_nl);
  assign VCOL_else_4_else_else_else_nor_1_tmp = ~((VCOL_x_sva[10:1]!=10'b0000000000));
  assign VCOL_else_4_else_else_else_unequal_tmp_1 = ~((VCOL_x_sva[0]) & VCOL_else_4_else_else_else_nor_1_tmp);
  assign VCOL_else_4_else_aif_equal_tmp = VCOL_x_sva == widthIn;
  assign VCOL_else_4_else_else_or_6_m1c_1 = VCOL_else_4_else_else_VCOL_else_4_else_else_nor_3_cse_1
      | (((~(VCOL_else_4_else_aif_equal_tmp | operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      | VROW_equal_tmp)) | VCOL_else_4_else_else_else_else_and_5_tmp_1) & VCOL_else_4_else_else_and_3_m1c_1);
  assign VCOL_else_4_else_else_and_3_m1c_1 = VCOL_else_4_else_else_else_unequal_tmp_1
      & (~ and_396_cse);
  assign VCOL_else_4_else_else_else_and_tmp_1 = (~ VROW_equal_tmp) & VCOL_else_4_else_else_else_unequal_tmp_1;
  assign VROW_equal_tmp = VROW_y_sva == heightIn;
  assign VCOL_else_4_else_else_and_7_m1c_1 = VCOL_else_4_else_else_else_unequal_tmp_1
      & (~ and_396_cse) & VCOL_else_4_VCOL_else_4_nor_1_m1c_1;
  assign VCOL_else_4_VCOL_else_4_nor_1_m1c_1 = ~(and_397_cse | and_431_cse);
  assign VCOL_else_4_else_else_else_else_and_5_tmp_1 = operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & (~ VROW_equal_tmp);
  assign VCOL_VCOL_nor_5_m1c_1 = ~(and_397_cse | VCOL_or_tmp_1);
  assign VCOL_or_tmp_1 = and_431_cse | VCOL_land_1_lpi_3_dfm_1;
  assign VCOL_VCOL_nor_1_m1c_1 = ~(and_431_cse | VCOL_land_1_lpi_3_dfm_1);
  assign VCOL_lor_lpi_3_dfm_1 = ~(nand_110_cse & VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1);
  assign VCOL_VCOL_and_3_nl = pix_result_11_lpi_3 & lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  assign VCOL_VCOL_and_4_nl = MUX_v_8_2_2(8'b00000000, pix_result_10_3_lpi_3, lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign VCOL_VCOL_and_5_nl = MUX_v_2_2_2(2'b00, pix_result_2_1_lpi_3, lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign VCOL_VCOL_and_6_nl = pix_result_0_lpi_3 & lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_4_nl = (operator_8_false_mul_itm_9_1_1[8:7]!=2'b00);
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_5_nl = MUX_v_7_2_2((operator_8_false_mul_itm_9_1_1[6:0]),
      7'b1111111, (operator_8_false_mul_itm_9_1_1[8]));
  assign nl_VCOL_else_5_if_for_acc_psp_sva_1 = conv_u2u_12_13({VCOL_VCOL_and_3_nl
      , VCOL_VCOL_and_4_nl , VCOL_VCOL_and_5_nl , VCOL_VCOL_and_6_nl}) + conv_u2u_8_13({VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_4_nl
      , VCOL_else_5_if_for_VCOL_else_5_if_for_VCOL_else_5_if_for_or_5_nl});
  assign VCOL_else_5_if_for_acc_psp_sva_1 = nl_VCOL_else_5_if_for_acc_psp_sva_1[12:0];
  assign operator_8_false_mux_cse = MUX_v_8_9_2(pix_0_lpi_3_dfm_10_mx1w0, pix_1_lpi_3_dfm_10_mx1w0,
      pix_2_lpi_3_dfm_9_mx1w0, pix_3_lpi_3_dfm_11, pix_4_lpi_3_dfm_1_mx0, VCOL_else_5_if_for_mux_87_cse,
      pix_6_lpi_3_dfm_9, pix_7_lpi_3_dfm_5_mx0, pix_8_lpi_3_dfm_8, reg_i_1_lpi_3_dfm_1_cse);
  assign VCOL_else_5_if_for_mux_90_nl = MUX_v_3_9_2(3'b001, 3'b010, 3'b001, 3'b010,
      3'b100, 3'b010, 3'b001, 3'b010, 3'b001, reg_i_1_lpi_3_dfm_1_cse);
  assign nl_operator_8_false_mul_nl = operator_8_false_mux_cse * VCOL_else_5_if_for_mux_90_nl;
  assign operator_8_false_mul_nl = nl_operator_8_false_mul_nl[9:0];
  assign operator_8_false_mul_itm_9_1_1 = readslicef_10_9_1(operator_8_false_mul_nl);
  assign VCOL_else_5_if_for_nand_14_nl = ~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva
      & (~((~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1) & VCOL_else_5_if_for_and_66_m1c_1)));
  assign VCOL_else_5_if_for_and_70_nl = operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      & VCOL_else_5_if_for_and_66_m1c_1;
  assign VCOL_else_5_if_for_and_67_nl = VCOL_or_9_tmp_1 & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign pix_3_lpi_3_dfm_11 = MUX1HOT_v_8_3_2(pix_3_lpi_3, (line_buf1_rsci_q_d[7:0]),
      pix_4_lpi_3_dfm_mx0, {VCOL_else_5_if_for_nand_14_nl , VCOL_else_5_if_for_and_70_nl
      , VCOL_else_5_if_for_and_67_nl});
  assign nand_55_nl = ~(operator_11_false_4_operator_11_false_4_nor_cse_sva_1 & exitL_exitL_exit_VCOL_else_5_if_for_1_sva);
  assign pix_4_lpi_3_dfm_1_mx0 = MUX_v_8_2_2((line_buf0_rsci_q_d[7:0]), pix_4_lpi_3,
      nand_55_nl);
  assign VCOL_else_5_if_for_nand_8_nl = ~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva
      & (~((((~ VCOL_else_4_else_else_else_else_and_5_tmp_1) & VCOL_else_4_else_else_and_7_m1c_1)
      | (and_396_cse & VCOL_else_4_VCOL_else_4_nor_1_m1c_1)) & VCOL_else_5_if_for_and_9_m1c_1)));
  assign VCOL_else_5_if_for_and_56_nl = ((VCOL_else_4_else_else_VCOL_else_4_else_else_nor_3_cse_1
      & VCOL_else_4_VCOL_else_4_nor_1_m1c_1) | and_431_cse) & VCOL_else_5_if_for_and_9_m1c_1;
  assign VCOL_else_5_if_for_and_58_nl = ((VCOL_else_4_else_else_else_else_and_5_tmp_1
      & VCOL_else_4_else_else_and_7_m1c_1) | VCOL_else_4_and_3_cse_1) & VCOL_else_5_if_for_and_9_m1c_1;
  assign pix_6_lpi_3_dfm_9 = MUX1HOT_v_8_4_2(pix_6_lpi_3, pix_3_lpi_3_dfm_mx0, pix_7_lpi_3,
      pix_4_lpi_3_dfm_mx0, {VCOL_else_5_if_for_nand_8_nl , VCOL_else_5_if_for_and_56_nl
      , VCOL_else_5_if_for_and_58_nl , VCOL_else_5_if_for_and_49_cse_1});
  assign VCOL_else_5_if_for_nand_6_nl = ~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva
      & (~((((~ VROW_equal_tmp) & VCOL_else_4_else_else_and_3_m1c_1 & VCOL_else_4_VCOL_else_4_nor_1_m1c_1)
      | VCOL_else_4_and_3_cse_1) & VCOL_else_5_if_for_and_9_m1c_1)));
  assign VCOL_else_5_if_for_or_7_nl = (VCOL_else_4_else_else_VCOL_else_4_else_else_nor_3_cse_1
      & VCOL_else_4_VCOL_else_4_nor_1_m1c_1 & VCOL_else_5_if_for_and_9_m1c_1) | VCOL_else_5_if_for_and_49_cse_1;
  assign VCOL_else_4_and_13_nl = ((VROW_equal_tmp & VCOL_else_4_else_else_and_3_m1c_1)
      | and_396_cse) & VCOL_else_4_VCOL_else_4_nor_1_m1c_1 & VCOL_else_5_if_for_and_9_m1c_1;
  assign pix_8_lpi_3_dfm_8 = MUX1HOT_v_8_4_2(pix_8_lpi_3, pix_5_lpi_3, pix_7_lpi_3,
      pix_4_lpi_3_dfm_mx0, {VCOL_else_5_if_for_nand_6_nl , VCOL_else_5_if_for_or_7_nl
      , VCOL_else_4_and_13_nl , VCOL_else_5_if_for_and_51_cse_1});
  assign nl_VCOL_x_sva_2 = VCOL_x_sva + 11'b00000000001;
  assign VCOL_x_sva_2 = nl_VCOL_x_sva_2[10:0];
  assign VCOL_or_1_cse_1 = VCOL_and_16_cse_1 | VCOL_equal_tmp_3_1;
  assign VCOL_and_6_m1c_1 = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 & VCOL_equal_tmp_2_1;
  assign VCOL_and_16_cse_1 = (~ lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) & VCOL_equal_tmp_2_1;
  assign VCOL_else_4_and_3_cse_1 = and_397_cse & (~ and_431_cse);
  assign VCOL_else_5_if_for_and_9_m1c_1 = (~ VCOL_land_1_lpi_3_dfm_1) & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign VCOL_else_4_else_else_VCOL_else_4_else_else_nor_3_cse_1 = ~(VCOL_else_4_else_else_else_unequal_tmp_1
      | and_396_cse);
  assign VCOL_else_5_if_for_and_49_cse_1 = VCOL_land_1_lpi_3_dfm_1 & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign VCOL_else_5_if_for_and_51_cse_1 = and_431_cse & VCOL_else_5_if_for_and_9_m1c_1;
  assign VCOL_else_5_if_for_and_66_m1c_1 = (~ VCOL_or_9_tmp_1) & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign VCOL_or_9_tmp_1 = (operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & (~ VROW_equal_tmp) & VCOL_else_4_else_else_else_unequal_tmp_1 & (~(and_396_cse
      | and_397_cse)) & VCOL_VCOL_nor_1_m1c_1) | (and_397_cse & VCOL_VCOL_nor_1_m1c_1)
      | VCOL_land_1_lpi_3_dfm_1;
  assign VCOL_else_5_if_for_and_50_m1c_1 = VCOL_else_4_VCOL_else_4_nor_1_m1c_1 &
      VCOL_else_5_if_for_and_9_m1c_1;
  assign VCOL_or_7_tmp_1 = (VCOL_else_4_else_aif_equal_tmp & VCOL_else_4_else_else_else_unequal_tmp_1
      & (~ and_396_cse) & VCOL_VCOL_nor_5_m1c_1) | (and_396_cse & VCOL_VCOL_nor_5_m1c_1)
      | (and_397_cse & (~ VCOL_or_tmp_1));
  assign VCOL_else_5_if_for_or_m1c_1 = (((~(VCOL_else_4_else_else_else_and_tmp_1
      | and_396_cse)) | ((~(VCOL_else_4_else_aif_equal_tmp | operator_10_false_1_operator_10_false_1_and_cse_sva_1_1))
      & VCOL_else_4_else_else_else_and_tmp_1)) & VCOL_and_m1c_1) | (and_431_cse &
      (~ VCOL_land_1_lpi_3_dfm_1) & exitL_exitL_exit_VCOL_else_5_if_for_1_sva);
  assign VCOL_and_m1c_1 = (~ and_397_cse) & VCOL_VCOL_nor_1_m1c_1 & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign max_val_10_3_lpi_3_dfm_mx0 = MUX_v_8_2_2(reg_max_val_10_3_lpi_3_dfm_1_1_cse,
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_sva_1, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1);
  assign VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_sva_1 = MUX_v_8_6_2(tmp_pix_0_lpi_3_mx0,
      tmp_pix_1_lpi_3_mx1, tmp_pix_2_lpi_3_mx1, tmp_pix_3_lpi_3_mx1, tmp_pix_4_lpi_3_mx1,
      tmp_pix_5_lpi_3_mx1, {j_2_0_lpi_3_dfm_3_1_rsp_0 , j_2_0_lpi_3_dfm_3_1_rsp_1});
  assign tmp_pix_mux_7_nl = MUX_v_8_2_2(tmp_pix_6_lpi_3, tmp_pix_6_lpi_3_dfm_2_mx2w1,
      VCOL_stage_0_2);
  assign tmp_pix_mux_11_nl = MUX_v_8_2_2(tmp_pix_7_lpi_3, tmp_pix_7_lpi_3_dfm_2_mx2w1,
      VCOL_stage_0_2);
  assign tmp_pix_mux_14_nl = MUX_v_8_2_2(tmp_pix_8_lpi_3, tmp_pix_8_lpi_3_dfm_2_mx2w1,
      VCOL_stage_0_2);
  assign operator_12_9_false_AC_TRN_AC_SAT_8_false_slc_tmp_pix_8_7_0_cse_sva_1 =
      MUX_v_8_9_2(tmp_pix_0_lpi_3_mx0, tmp_pix_1_lpi_3_mx1, tmp_pix_2_lpi_3_mx1,
      tmp_pix_3_lpi_3_mx1, tmp_pix_4_lpi_3_mx1, tmp_pix_5_lpi_3_mx1, tmp_pix_mux_7_nl,
      tmp_pix_mux_11_nl, tmp_pix_mux_14_nl, {i_lpi_3_dfm_mx0_3 , i_lpi_3_dfm_mx0_2_0});
  assign nl_operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_nl = ({1'b1 , (~ operator_12_9_false_AC_TRN_AC_SAT_8_false_slc_tmp_pix_8_7_0_cse_sva_1)})
      + conv_u2s_8_9(max_val_10_3_lpi_3_dfm_mx0) + 9'b000000001;
  assign operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_nl = nl_operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_nl[8:0];
  assign operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8 = readslicef_9_1_8(operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_nl);
  assign VCOL_else_5_else_if_for_and_stg_1_1_sva_1 = (reg_i_1_lpi_3_dfm_1_cse[1:0]==2'b01);
  assign VCOL_else_5_else_if_for_and_stg_1_2_sva_1 = (reg_i_1_lpi_3_dfm_1_cse[1:0]==2'b10);
  assign VCOL_else_5_else_if_for_and_stg_1_3_sva_1 = (reg_i_1_lpi_3_dfm_1_cse[1:0]==2'b11);
  assign VCOL_else_5_else_if_for_and_stg_2_0_sva_1 = VCOL_else_5_else_if_for_and_stg_1_0_sva_1
      & (~ (reg_i_1_lpi_3_dfm_1_cse[2]));
  assign VCOL_else_5_else_if_for_and_stg_1_0_sva_1 = ~((reg_i_1_lpi_3_dfm_1_cse[1:0]!=2'b00));
  assign VCOL_else_5_else_if_for_1_and_stg_1_1_sva_1 = max_i_2_0_lpi_3_dfm_1_1_0
      & (~ (max_i_2_0_lpi_3_dfm_1_1_2_1[0]));
  assign VCOL_else_5_else_if_for_1_and_stg_1_2_sva_1 = (~ max_i_2_0_lpi_3_dfm_1_1_0)
      & (max_i_2_0_lpi_3_dfm_1_1_2_1[0]);
  assign VCOL_else_5_else_if_for_1_and_stg_1_3_sva_1 = max_i_2_0_lpi_3_dfm_1_1_0
      & (max_i_2_0_lpi_3_dfm_1_1_2_1[0]);
  assign VCOL_else_5_else_if_for_1_and_stg_2_0_sva_1 = VCOL_else_5_else_if_for_1_and_stg_1_0_sva_1
      & (~ (max_i_2_0_lpi_3_dfm_1_1_2_1[1]));
  assign VCOL_else_5_else_if_for_1_and_stg_1_0_sva_1 = ~(max_i_2_0_lpi_3_dfm_1_1_0
      | (max_i_2_0_lpi_3_dfm_1_1_2_1[0]));
  assign VCOL_else_5_else_if_for_and_20_tmp_1 = VCOL_else_5_else_if_for_and_stg_2_0_sva_1
      & (reg_i_1_lpi_3_dfm_1_cse[3]);
  assign VCOL_else_5_else_if_for_1_for_and_8_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_2_0_sva_1
      & max_i_3_lpi_3_dfm_1_1 & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_else_if_for_and_18_tmp_1 = VCOL_else_5_else_if_for_and_stg_1_3_sva_1
      & (reg_i_1_lpi_3_dfm_1_cse[3:2]==2'b01);
  assign VCOL_else_5_else_if_for_1_for_and_7_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_1_3_sva_1
      & (max_i_2_0_lpi_3_dfm_1_1_2_1[1]) & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_else_if_for_and_16_tmp_1 = VCOL_else_5_else_if_for_and_stg_1_2_sva_1
      & (reg_i_1_lpi_3_dfm_1_cse[3:2]==2'b01);
  assign VCOL_else_5_else_if_for_1_for_and_6_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_1_2_sva_1
      & (max_i_2_0_lpi_3_dfm_1_1_2_1[1]) & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_else_if_for_and_14_tmp_1 = VCOL_else_5_else_if_for_and_stg_1_1_sva_1
      & (reg_i_1_lpi_3_dfm_1_cse[3:2]==2'b01);
  assign VCOL_else_5_else_if_for_1_for_and_5_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_1_1_sva_1
      & (max_i_2_0_lpi_3_dfm_1_1_2_1[1]) & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_else_if_for_and_12_tmp_1 = VCOL_else_5_else_if_for_and_stg_1_0_sva_1
      & (reg_i_1_lpi_3_dfm_1_cse[3:2]==2'b01);
  assign VCOL_else_5_else_if_for_1_for_and_4_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_1_0_sva_1
      & (max_i_2_0_lpi_3_dfm_1_1_2_1[1]) & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_else_if_for_and_13_tmp_1 = VCOL_else_5_else_if_for_and_stg_1_3_sva_1
      & (reg_i_1_lpi_3_dfm_1_cse[3:2]==2'b00);
  assign VCOL_else_5_else_if_for_1_for_and_3_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_1_3_sva_1
      & (~ (max_i_2_0_lpi_3_dfm_1_1_2_1[1])) & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_else_if_for_and_15_tmp_1 = VCOL_else_5_else_if_for_and_stg_1_2_sva_1
      & (reg_i_1_lpi_3_dfm_1_cse[3:2]==2'b00);
  assign VCOL_else_5_else_if_for_1_for_and_2_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_1_2_sva_1
      & (~ (max_i_2_0_lpi_3_dfm_1_1_2_1[1])) & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_else_if_for_and_17_tmp_1 = VCOL_else_5_else_if_for_and_stg_1_1_sva_1
      & (reg_i_1_lpi_3_dfm_1_cse[3:2]==2'b00);
  assign VCOL_else_5_else_if_for_1_for_and_1_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_1_1_sva_1
      & (~ (max_i_2_0_lpi_3_dfm_1_1_2_1[1])) & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_else_if_for_and_19_tmp_1 = VCOL_else_5_else_if_for_and_stg_2_0_sva_1
      & (~ (reg_i_1_lpi_3_dfm_1_cse[3]));
  assign VCOL_else_5_else_if_for_1_for_and_tmp_1 = VCOL_else_5_else_if_for_1_and_stg_2_0_sva_1
      & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1;
  assign VCOL_else_5_if_for_and_46_nl = (~ VCOL_else_4_else_aif_equal_tmp) & exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  assign VCOL_else_5_if_for_mux_78_tmp_0 = MUX_s_1_2_2((VCOL_x_sva[0]), (VCOL_x_sva_2[0]),
      VCOL_else_5_if_for_and_46_nl);
  assign and_dcpl_1 = VCOL_stage_0_1 & (~ operator_11_false_4_operator_11_false_4_nor_tmp);
  assign and_dcpl_4 = VCOL_else_4_else_aif_equal_tmp & exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1;
  assign or_dcpl_4 = ~((~(and_dcpl_4 & VCOL_stage_0_2)) & VCOL_stage_0_1);
  assign mux_tmp_8 = MUX_s_1_2_2((~ exitL_exitL_exit_VCOL_else_5_if_for_1_sva), lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0,
      VCOL_stage_0_2);
  assign or_tmp_20 = (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) | VCOL_else_4_else_aif_equal_tmp
      | (~ operator_11_false_4_operator_11_false_4_nor_tmp);
  assign mux_tmp_16 = MUX_s_1_2_2((~ (ctrl_signal_rsci_idat[0])), (ctrl_signal_rsci_idat[0]),
      ctrl_signal_rsci_idat[1]);
  assign or_tmp_41 = (ctrl_signal_rsci_idat!=2'b10);
  assign and_dcpl_16 = mux_372_cse & VCOL_stage_0_1 & operator_4_false_3_acc_itm_4;
  assign or_dcpl_40 = ~(exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 & VCOL_stage_0_2);
  assign mux_217_nl = MUX_s_1_2_2(or_774_cse, (~ VCOL_else_4_else_aif_equal_tmp),
      exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_218_nl = MUX_s_1_2_2(or_72_cse, mux_217_nl, VCOL_stage_0_2);
  assign and_dcpl_25 = mux_218_nl & VCOL_stage_0_1;
  assign mux_234_nl = MUX_s_1_2_2(or_774_cse, or_tmp_41, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_tmp_236 = MUX_s_1_2_2(or_tmp_41, mux_234_nl, VCOL_stage_0_2);
  assign nor_tmp_55 = (operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1
      | (VCOL_else_3_else_asn_itm_1!=10'b0000000000)) & exitL_exitL_exit_VCOL_else_5_if_for_1_sva;
  assign and_dcpl_51 = (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) & VCOL_stage_0_2;
  assign and_dcpl_53 = or_564_cse & VCOL_stage_0_2;
  assign mux_263_itm = MUX_s_1_2_2(exitL_exitL_exit_VCOL_else_5_if_for_1_sva, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1,
      VCOL_stage_0_2);
  assign lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_mx0c1 = nand_142_cse & VCOL_stage_0_1
      & (fsm_output[1]);
  assign mux_240_nl = MUX_s_1_2_2(or_tmp_41, or_593_cse, nor_16_cse);
  assign or_334_nl = (~ operator_4_false_2_acc_itm_2) | operator_4_false_3_acc_itm_4
      | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10);
  assign mux_237_nl = MUX_s_1_2_2(or_334_nl, or_774_cse, or_495_cse);
  assign mux_238_nl = MUX_s_1_2_2(mux_237_nl, or_775_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_241_nl = MUX_s_1_2_2(mux_240_nl, mux_238_nl, VCOL_stage_0_2);
  assign j_2_0_lpi_3_dfm_3_1_mx1c0 = (~ mux_241_nl) & VCOL_stage_0_1;
  assign nor_119_nl = ~((~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0
      | operator_4_false_2_acc_itm_2 | operator_4_false_3_acc_itm_4);
  assign mux_245_nl = MUX_s_1_2_2(or_tmp_41, nor_119_nl, nor_16_cse);
  assign or_342_nl = nor_238_cse | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10);
  assign mux_244_nl = MUX_s_1_2_2(or_342_nl, or_775_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_246_nl = MUX_s_1_2_2(mux_245_nl, mux_244_nl, VCOL_stage_0_2);
  assign j_2_0_lpi_3_dfm_3_1_mx1c3 = mux_246_nl | (~ VCOL_stage_0_1);
  assign operator_4_false_mux_nl = MUX_v_2_2_2(j_2_0_lpi_3_dfm_3_1_rsp_0, (operator_4_false_acc_psp_sva_1[2:1]),
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1);
  assign operator_4_false_mux_2_nl = MUX_s_1_2_2(j_2_0_lpi_3_dfm_3_1_rsp_1, (operator_4_false_acc_psp_sva_1[0]),
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1);
  assign nl_operator_4_false_2_acc_nl = ({operator_4_false_mux_nl , operator_4_false_mux_2_nl})
      + 3'b011;
  assign operator_4_false_2_acc_nl = nl_operator_4_false_2_acc_nl[2:0];
  assign operator_4_false_2_acc_itm_2 = readslicef_3_1_2(operator_4_false_2_acc_nl);
  assign nl_operator_11_false_acc_nl = ({1'b1 , widthIn}) + conv_u2s_11_12(~ VCOL_x_sva_mx1);
  assign operator_11_false_acc_nl = nl_operator_11_false_acc_nl[11:0];
  assign operator_11_false_acc_itm_11_1 = readslicef_12_1_11(operator_11_false_acc_nl);
  assign VCOL_if_3_not_nl = ~ operator_11_false_4_operator_11_false_4_nor_tmp;
  assign line_buf0_rsci_adr_d_pff = MUX_v_10_2_2(10'b0000000000, z_out, VCOL_if_3_not_nl);
  assign VCOL_else_5_if_for_mux_80_nl = MUX_v_8_2_2(VCOL_VCOL_slc_pix_47_40_2_lpi_4,
      pix_2_lpi_3_dfm_9_mx1w0, VCOL_stage_0_2);
  assign VCOL_else_5_if_for_mux_79_nl = MUX_v_8_2_2(VCOL_VCOL_slc_pix_71_64_lpi_4,
      VCOL_else_5_if_for_mux_87_cse, VCOL_stage_0_2);
  assign line_buf0_rsci_d_d = {VCOL_else_5_if_for_mux_80_nl , VCOL_else_5_if_for_mux_79_nl};
  assign line_buf0_rsci_we_d_pff = mux_262_cse & and_dcpl_1 & (fsm_output[1]);
  assign and_255_nl = exitL_exitL_exit_VCOL_else_5_if_for_1_sva & operator_11_false_4_operator_11_false_4_nor_tmp;
  assign mux_259_nl = MUX_s_1_2_2(and_255_nl, exitL_exitL_exit_VCOL_else_5_if_for_1_sva,
      VCOL_x_sva[0]);
  assign or_359_nl = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0 | (~
      operator_11_false_4_operator_11_false_4_nor_tmp);
  assign mux_258_nl = MUX_s_1_2_2(or_359_nl, lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0,
      VCOL_else_5_if_for_mux_78_tmp_0);
  assign mux_260_nl = MUX_s_1_2_2(mux_259_nl, (~ mux_258_nl), VCOL_stage_0_2);
  assign line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_pff = mux_260_nl & VCOL_stage_0_1
      & (fsm_output[1]);
  assign VCOL_mux_40_nl = MUX_v_8_2_2(VCOL_VCOL_slc_pix_39_32_2_lpi_4, VCOL_VCOL_slc_pix_39_32_2_lpi_3_dfm_mx1w0,
      VCOL_stage_0_2);
  assign VCOL_else_5_if_for_mux_78_nl = MUX_v_8_2_2(VCOL_VCOL_slc_pix_63_56_lpi_4,
      pix_4_lpi_3_dfm_1_mx0, VCOL_stage_0_2);
  assign line_buf1_rsci_d_d = {VCOL_mux_40_nl , VCOL_else_5_if_for_mux_78_nl};
  assign nor_123_nl = ~((VCOL_x_sva[0]) | (~(exitL_exitL_exit_VCOL_else_5_if_for_1_sva
      & VCOL_if_6_VCOL_if_6_or_cse)));
  assign nor_124_nl = ~(VCOL_else_5_if_for_mux_78_tmp_0 | (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1)
      | VCOL_else_4_else_aif_equal_tmp | (~ VCOL_if_6_VCOL_if_6_or_cse));
  assign mux_257_nl = MUX_s_1_2_2(nor_123_nl, nor_124_nl, VCOL_stage_0_2);
  assign line_buf1_rsci_we_d_pff = mux_257_nl & and_dcpl_1 & (fsm_output[1]);
  assign or_463_nl = (~ VCOL_stage_0_2) | (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1)
      | VCOL_else_4_else_aif_equal_tmp;
  assign mux_tmp = MUX_s_1_2_2((VCOL_x_sva_2[0]), (VCOL_x_sva[0]), or_463_nl);
  assign or_tmp_386 = (~ mux_tmp) & (fsm_output[1]);
  assign and_dcpl_66 = VCOL_stage_0_1 & run_wen;
  assign and_dcpl_91 = exitL_exitL_exit_VCOL_else_5_if_for_1_sva & VCOL_stage_0_2;
  assign or_tmp_428 = (~(reg_operator_11_false_6_nor_itm_1_cse | (~ VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1)))
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_land_1_lpi_3_dfm_1;
  assign nor_286_nl = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 |
      (VCOL_x_sva[10:1]!=10'b0000000000) | or_tmp_428);
  assign nor_287_nl = ~((~ reg_operator_11_false_6_nor_itm_1_cse) | operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      | VCOL_land_1_lpi_3_dfm_1);
  assign mux_300_nl = MUX_s_1_2_2(nor_286_nl, nor_287_nl, VROW_equal_tmp);
  assign nand_tmp_18 = ~((VCOL_x_sva[0]) & mux_300_nl);
  assign nor_148_cse = ~(VROW_equal_tmp | (~ operator_10_false_1_operator_10_false_1_and_cse_sva_1_1));
  assign or_517_nl = nor_148_cse | VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_land_1_lpi_3_dfm_1;
  assign or_516_nl = (VCOL_x_sva[10:1]!=10'b0000000000) | or_tmp_428;
  assign mux_301_nl = MUX_s_1_2_2(or_tmp_428, or_516_nl, nor_148_cse);
  assign mux_tmp_299 = MUX_s_1_2_2(or_517_nl, mux_301_nl, VCOL_x_sva[0]);
  assign or_529_nl = (VCOL_x_sva[0]) | VCOL_land_1_lpi_3_dfm_1;
  assign or_528_nl = (((~ VROW_equal_tmp) | reg_operator_11_false_6_nor_itm_1_cse)
      & (VCOL_x_sva[0])) | VCOL_land_1_lpi_3_dfm_1;
  assign mux_311_nl = MUX_s_1_2_2(or_528_nl, VCOL_or_tmp_1, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign mux_tmp_309 = MUX_s_1_2_2(or_529_nl, mux_311_nl, VCOL_else_4_else_aif_equal_tmp);
  assign nor_289_cse = ~(and_429_cse | VCOL_land_1_lpi_3_dfm_1);
  assign nand_69_nl = ~((~(VCOL_else_4_else_aif_equal_tmp | (~ VROW_equal_tmp)))
      & nor_289_cse);
  assign mux_tmp_317 = MUX_s_1_2_2(VCOL_or_tmp_1, nand_69_nl, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign or_544_nl = (((~ VCOL_else_4_else_aif_equal_tmp) | (~ VROW_equal_tmp) |
      reg_operator_11_false_6_nor_itm_1_cse) & (VCOL_x_sva[0])) | VCOL_land_1_lpi_3_dfm_1;
  assign or_542_nl = VCOL_else_4_else_aif_equal_tmp | (~ VROW_equal_tmp) | (VCOL_x_sva[0])
      | VCOL_land_1_lpi_3_dfm_1;
  assign mux_tmp_321 = MUX_s_1_2_2(or_544_nl, or_542_nl, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign nand_tmp_22 = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & VCOL_else_4_else_aif_equal_tmp & nor_289_cse);
  assign mux_tmp_329 = MUX_s_1_2_2(VCOL_land_1_lpi_3_dfm_1, nand_tmp_22, VROW_equal_tmp);
  assign or_556_nl = ((~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & VCOL_else_4_else_aif_equal_tmp)) & (VCOL_x_sva[0])) | VCOL_land_1_lpi_3_dfm_1;
  assign mux_tmp_333 = MUX_s_1_2_2(or_556_nl, nand_tmp_22, VROW_equal_tmp);
  assign or_tmp_477 = (VROW_y_sva!=10'b0000000001);
  assign and_tmp_25 = (VCOL_x_sva_2[0]) & or_tmp_477;
  assign not_tmp_284 = ~((VCOL_x_sva!=11'b00000000001));
  assign or_tmp_484 = (~ operator_10_false_1_operator_10_false_1_and_cse_sva_1_1)
      | VROW_equal_tmp | not_tmp_284;
  assign not_tmp_287 = ~((~ VCOL_stage_0_1) | (VCOL_x_sva_2[10:1]!=10'b0000000000)
      | and_tmp_25);
  assign nand_tmp_25 = ~(operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1
      & (~ VCOL_else_5_if_for_and_6_cse));
  assign or_578_nl = operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | (~ exitL_exitL_exit_VCOL_else_5_if_for_1_sva);
  assign mux_tmp_348 = MUX_s_1_2_2(or_578_nl, VCOL_else_5_if_for_and_6_cse, operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1);
  assign or_tmp_497 = (~((VCOL_x_sva[0]) | reg_operator_11_false_6_nor_itm_1_cse))
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_and_37_itm_1;
  assign or_tmp_501 = ~(nand_112_cse & or_tmp_497);
  assign or_tmp_504 = VCOL_equal_tmp_1 | VCOL_equal_tmp_1_1 | (exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1
      & VCOL_equal_tmp_2_1 & lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3);
  assign not_tmp_297 = ~(VCOL_stage_0_1 | (~ or_tmp_504));
  assign and_456_nl = exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1 & lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3;
  assign mux_369_nl = MUX_s_1_2_2((~ VCOL_equal_tmp_3_1), and_456_nl, VCOL_equal_tmp_2_1);
  assign or_tmp_507 = VCOL_equal_tmp_1 | mux_369_nl;
  assign and_dcpl_123 = VCOL_stage_0_2 & VCOL_equal_tmp_2_1;
  assign or_tmp_514 = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0001);
  assign nor_297_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (~((reg_i_1_lpi_3_dfm_1_cse!=4'b0001))));
  assign mux_375_nl = MUX_s_1_2_2(or_tmp_514, nor_297_nl, max_i_2_0_lpi_3_dfm_1_1_0);
  assign or_599_nl = max_i_3_lpi_3_dfm_1_1 | (~ VCOL_else_5_else_if_for_1_for_not_mdf_sva_1)
      | (max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b00);
  assign mux_tmp_373 = MUX_s_1_2_2(mux_375_nl, or_tmp_514, or_599_nl);
  assign or_608_nl = (~((max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b00) | (~ max_i_2_0_lpi_3_dfm_1_1_0)))
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0001);
  assign mux_378_nl = MUX_s_1_2_2(or_608_nl, mux_tmp_373, max_i_3_lpi_3_dfm_3_1);
  assign or_789_nl = (~((~ j_2_0_lpi_3_dfm_3_1_rsp_1) | (j_2_0_lpi_3_dfm_3_1_rsp_0!=2'b00)))
      | mux_tmp_373;
  assign mux_379_nl = MUX_s_1_2_2(mux_378_nl, or_789_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign or_790_nl = (~((i_lpi_3_dfm_2_1!=4'b0001))) | mux_tmp_373;
  assign or_605_nl = (~((operator_4_false_acc_psp_sva_1!=3'b001))) | mux_tmp_373;
  assign mux_377_nl = MUX_s_1_2_2(or_790_nl, or_605_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign mux_380_nl = MUX_s_1_2_2(mux_379_nl, mux_377_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign mux_tmp_378 = MUX_s_1_2_2(mux_380_nl, mux_tmp_373, operator_4_false_3_acc_itm_4);
  assign nand_tmp_28 = (~((i_1_lpi_3_dfm_1_1!=4'b0001))) | mux_tmp_373;
  assign or_tmp_530 = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0101);
  assign nor_302_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (~((reg_i_1_lpi_3_dfm_1_cse!=4'b0101))));
  assign mux_390_nl = MUX_s_1_2_2(or_tmp_530, nor_302_nl, max_i_2_0_lpi_3_dfm_1_1_0);
  assign or_615_nl = max_i_3_lpi_3_dfm_1_1 | (~ VCOL_else_5_else_if_for_1_for_not_mdf_sva_1)
      | (max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b10);
  assign mux_tmp_388 = MUX_s_1_2_2(mux_390_nl, or_tmp_530, or_615_nl);
  assign or_624_nl = (~((max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b10) | (~ max_i_2_0_lpi_3_dfm_1_1_0)))
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0101);
  assign mux_393_nl = MUX_s_1_2_2(or_624_nl, mux_tmp_388, max_i_3_lpi_3_dfm_3_1);
  assign or_792_nl = (~((~ j_2_0_lpi_3_dfm_3_1_rsp_1) | (j_2_0_lpi_3_dfm_3_1_rsp_0!=2'b10)))
      | mux_tmp_388;
  assign mux_394_nl = MUX_s_1_2_2(mux_393_nl, or_792_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign or_793_nl = (~((i_lpi_3_dfm_2_1!=4'b0101))) | mux_tmp_388;
  assign or_621_nl = (~((operator_4_false_acc_psp_sva_1!=3'b101))) | mux_tmp_388;
  assign mux_392_nl = MUX_s_1_2_2(or_793_nl, or_621_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign mux_395_nl = MUX_s_1_2_2(mux_394_nl, mux_392_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign mux_tmp_393 = MUX_s_1_2_2(mux_395_nl, mux_tmp_388, operator_4_false_3_acc_itm_4);
  assign or_tmp_540 = (~((i_1_lpi_3_dfm_1_1!=4'b0101))) | mux_tmp_388;
  assign nor_306_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (~((reg_i_1_lpi_3_dfm_1_cse!=4'b0010))));
  assign or_633_nl = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0010);
  assign or_632_nl = max_i_3_lpi_3_dfm_1_1 | (~ VCOL_else_5_else_if_for_1_for_not_mdf_sva_1)
      | (max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b01) | max_i_2_0_lpi_3_dfm_1_1_0;
  assign mux_tmp_402 = MUX_s_1_2_2(nor_306_nl, or_633_nl, or_632_nl);
  assign or_641_nl = (~((max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b01) | max_i_2_0_lpi_3_dfm_1_1_0))
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0010);
  assign mux_407_nl = MUX_s_1_2_2(or_641_nl, mux_tmp_402, max_i_3_lpi_3_dfm_3_1);
  assign or_639_nl = (~(j_2_0_lpi_3_dfm_3_1_rsp_1 | (j_2_0_lpi_3_dfm_3_1_rsp_0!=2'b01)))
      | mux_tmp_402;
  assign mux_408_nl = MUX_s_1_2_2(mux_407_nl, or_639_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign or_794_nl = (~((i_lpi_3_dfm_2_1!=4'b0010))) | mux_tmp_402;
  assign or_795_nl = (~((operator_4_false_acc_psp_sva_1!=3'b010))) | mux_tmp_402;
  assign mux_406_nl = MUX_s_1_2_2(or_794_nl, or_795_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign mux_409_nl = MUX_s_1_2_2(mux_408_nl, mux_406_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign mux_tmp_407 = MUX_s_1_2_2(mux_409_nl, mux_tmp_402, operator_4_false_3_acc_itm_4);
  assign nand_tmp_35 = (~((i_1_lpi_3_dfm_1_1!=4'b0010))) | mux_tmp_402;
  assign nor_312_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (~((reg_i_1_lpi_3_dfm_1_cse!=4'b0110))));
  assign or_651_nl = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0110);
  assign or_650_nl = max_i_3_lpi_3_dfm_1_1 | (~ VCOL_else_5_else_if_for_1_for_not_mdf_sva_1)
      | (max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b11) | max_i_2_0_lpi_3_dfm_1_1_0;
  assign mux_tmp_416 = MUX_s_1_2_2(nor_312_nl, or_651_nl, or_650_nl);
  assign or_659_nl = (~((max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b11) | max_i_2_0_lpi_3_dfm_1_1_0))
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0110);
  assign mux_421_nl = MUX_s_1_2_2(or_659_nl, mux_tmp_416, max_i_3_lpi_3_dfm_3_1);
  assign or_657_nl = (~(j_2_0_lpi_3_dfm_3_1_rsp_1 | (j_2_0_lpi_3_dfm_3_1_rsp_0!=2'b11)))
      | mux_tmp_416;
  assign mux_422_nl = MUX_s_1_2_2(mux_421_nl, or_657_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign or_797_nl = (~((i_lpi_3_dfm_2_1!=4'b0110))) | mux_tmp_416;
  assign or_798_nl = (~((operator_4_false_acc_psp_sva_1!=3'b110))) | mux_tmp_416;
  assign mux_420_nl = MUX_s_1_2_2(or_797_nl, or_798_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign mux_423_nl = MUX_s_1_2_2(mux_422_nl, mux_420_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign mux_tmp_421 = MUX_s_1_2_2(mux_423_nl, mux_tmp_416, operator_4_false_3_acc_itm_4);
  assign or_tmp_574 = (~((i_1_lpi_3_dfm_1_1!=4'b0110))) | mux_tmp_416;
  assign not_tmp_319 = ~((reg_i_1_lpi_3_dfm_1_cse[1:0]==2'b11));
  assign or_670_nl = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse[3:2]!=2'b00)
      | not_tmp_319;
  assign or_668_nl = (reg_i_1_lpi_3_dfm_1_cse[3:2]!=2'b00) | not_tmp_319;
  assign or_666_nl = (~ VCOL_else_5_else_if_for_1_for_not_mdf_sva_1) | max_i_3_lpi_3_dfm_1_1;
  assign mux_433_nl = MUX_s_1_2_2(or_668_nl, or_666_nl, lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3);
  assign mux_tmp_431 = MUX_s_1_2_2(or_670_nl, mux_433_nl, nor_211_cse);
  assign or_tmp_599 = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0111);
  assign nor_316_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | ((reg_i_1_lpi_3_dfm_1_cse==4'b0111)));
  assign and_459_nl = VCOL_else_5_else_if_for_1_for_not_mdf_sva_1 & (max_i_2_0_lpi_3_dfm_1_1_2_1==2'b11)
      & max_i_2_0_lpi_3_dfm_1_1_0;
  assign mux_447_nl = MUX_s_1_2_2(or_tmp_599, nor_316_nl, and_459_nl);
  assign mux_tmp_445 = MUX_s_1_2_2(mux_447_nl, or_tmp_599, max_i_3_lpi_3_dfm_1_1);
  assign or_693_nl = ((max_i_2_0_lpi_3_dfm_1_1_2_1==2'b11) & max_i_2_0_lpi_3_dfm_1_1_0)
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0111);
  assign mux_450_nl = MUX_s_1_2_2(or_693_nl, mux_tmp_445, max_i_3_lpi_3_dfm_3_1);
  assign or_692_nl = (j_2_0_lpi_3_dfm_3_1_rsp_1 & (j_2_0_lpi_3_dfm_3_1_rsp_0==2'b11))
      | mux_tmp_445;
  assign mux_451_nl = MUX_s_1_2_2(mux_450_nl, or_692_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign or_799_nl = ((i_lpi_3_dfm_2_1==4'b0111)) | mux_tmp_445;
  assign or_690_nl = ((operator_4_false_acc_psp_sva_1==3'b111)) | mux_tmp_445;
  assign mux_449_nl = MUX_s_1_2_2(or_799_nl, or_690_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign mux_452_nl = MUX_s_1_2_2(mux_451_nl, mux_449_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign mux_tmp_450 = MUX_s_1_2_2(mux_452_nl, mux_tmp_445, operator_4_false_3_acc_itm_4);
  assign or_tmp_609 = ((i_1_lpi_3_dfm_1_1==4'b0111)) | mux_tmp_445;
  assign nor_318_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (~((reg_i_1_lpi_3_dfm_1_cse!=4'b0000))));
  assign or_702_nl = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0000);
  assign or_701_nl = max_i_3_lpi_3_dfm_1_1 | (~ VCOL_else_5_else_if_for_1_for_not_mdf_sva_1)
      | (max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b00) | max_i_2_0_lpi_3_dfm_1_1_0;
  assign mux_tmp_459 = MUX_s_1_2_2(nor_318_nl, or_702_nl, or_701_nl);
  assign nor_319_cse = ~((max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b00) | max_i_2_0_lpi_3_dfm_1_1_0);
  assign or_709_nl = nor_319_cse | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0000);
  assign mux_464_nl = MUX_s_1_2_2(or_709_nl, mux_tmp_459, max_i_3_lpi_3_dfm_3_1);
  assign or_800_nl = (~(j_2_0_lpi_3_dfm_3_1_rsp_1 | (j_2_0_lpi_3_dfm_3_1_rsp_0!=2'b00)))
      | mux_tmp_459;
  assign mux_465_nl = MUX_s_1_2_2(mux_464_nl, or_800_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign or_801_nl = (~((i_lpi_3_dfm_2_1!=4'b0000))) | mux_tmp_459;
  assign or_802_nl = (~((operator_4_false_acc_psp_sva_1!=3'b000))) | mux_tmp_459;
  assign mux_463_nl = MUX_s_1_2_2(or_801_nl, or_802_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign mux_466_nl = MUX_s_1_2_2(mux_465_nl, mux_463_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign nand_tmp_44 = ~(operator_4_false_2_acc_itm_2 & (~ mux_466_nl));
  assign nand_tmp_45 = (~((i_1_lpi_3_dfm_1_1!=4'b0000))) | mux_tmp_459;
  assign nor_325_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (~((reg_i_1_lpi_3_dfm_1_cse!=4'b1000))));
  assign or_717_nl = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b1000);
  assign or_715_nl = (~ max_i_3_lpi_3_dfm_1_1) | (~ VCOL_else_5_else_if_for_1_for_not_mdf_sva_1)
      | (max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b00) | max_i_2_0_lpi_3_dfm_1_1_0;
  assign mux_tmp_469 = MUX_s_1_2_2(nor_325_nl, or_717_nl, or_715_nl);
  assign or_725_nl = nor_319_cse | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b1000);
  assign mux_473_nl = MUX_s_1_2_2(mux_tmp_469, or_725_nl, max_i_3_lpi_3_dfm_3_1);
  assign or_722_nl = (~((i_lpi_3_dfm_2_1!=4'b1000))) | mux_tmp_469;
  assign mux_tmp_471 = MUX_s_1_2_2(mux_473_nl, or_722_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign nand_tmp_46 = (~((i_1_lpi_3_dfm_1_1!=4'b1000))) | mux_tmp_469;
  assign nor_329_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (~((reg_i_1_lpi_3_dfm_1_cse!=4'b0100))));
  assign or_735_nl = lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0100);
  assign or_734_nl = max_i_3_lpi_3_dfm_1_1 | (~ VCOL_else_5_else_if_for_1_for_not_mdf_sva_1)
      | (max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b10) | max_i_2_0_lpi_3_dfm_1_1_0;
  assign mux_tmp_481 = MUX_s_1_2_2(nor_329_nl, or_735_nl, or_734_nl);
  assign or_743_nl = (~((max_i_2_0_lpi_3_dfm_1_1_2_1!=2'b10) | max_i_2_0_lpi_3_dfm_1_1_0))
      | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse!=4'b0100);
  assign mux_486_nl = MUX_s_1_2_2(or_743_nl, mux_tmp_481, max_i_3_lpi_3_dfm_3_1);
  assign or_805_nl = (~(j_2_0_lpi_3_dfm_3_1_rsp_1 | (j_2_0_lpi_3_dfm_3_1_rsp_0!=2'b10)))
      | mux_tmp_481;
  assign mux_487_nl = MUX_s_1_2_2(mux_486_nl, or_805_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign or_806_nl = (~((i_lpi_3_dfm_2_1!=4'b0100))) | mux_tmp_481;
  assign or_807_nl = (~((operator_4_false_acc_psp_sva_1!=3'b100))) | mux_tmp_481;
  assign mux_485_nl = MUX_s_1_2_2(or_806_nl, or_807_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign mux_488_nl = MUX_s_1_2_2(mux_487_nl, mux_485_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign mux_tmp_486 = MUX_s_1_2_2(mux_488_nl, mux_tmp_481, operator_4_false_3_acc_itm_4);
  assign or_tmp_659 = (~((i_1_lpi_3_dfm_1_1!=4'b0100))) | mux_tmp_481;
  assign nor_334_nl = ~(max_i_2_0_lpi_3_dfm_1_1_0 | (~ lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3));
  assign and_465_nl = max_i_2_0_lpi_3_dfm_1_1_0 & lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3;
  assign mux_tmp_495 = MUX_s_1_2_2(nor_334_nl, and_465_nl, j_2_0_lpi_3_dfm_3_1_rsp_1);
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_x_sva <= 11'b00000000000;
    end
    else if ( rst ) begin
      VCOL_x_sva <= 11'b00000000000;
    end
    else if ( (VCOL_x_and_cse | (fsm_output[2]) | (fsm_output[0])) & run_wen ) begin
      VCOL_x_sva <= MUX_v_11_2_2(11'b00000000000, VCOL_x_sva_mx1, not_687_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VROW_y_sva <= 10'b0000000000;
    end
    else if ( rst ) begin
      VROW_y_sva <= 10'b0000000000;
    end
    else if ( run_wen & VROW_y_or_cse ) begin
      VROW_y_sva <= MUX_v_10_2_2(10'b0000000000, z_out, VROW_y_not_2_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dat_out_rsci_idat <= 8'b00000000;
    end
    else if ( rst ) begin
      dat_out_rsci_idat <= 8'b00000000;
    end
    else if ( run_wen & (~((~ (fsm_output[1])) | or_dcpl_40 | (~ VCOL_if_6_VCOL_if_6_and_itm_1)))
        ) begin
      dat_out_rsci_idat <= MUX_v_8_2_2(pix_result_10_3_lpi_3_dfm_3_mx1w0, 8'b11111111,
          (readslicef_13_1_12(operator_12_9_false_AC_TRN_AC_SAT_acc_nl)));
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1 <= 1'b0;
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0 <= 1'b0;
    end
    else if ( rst ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1 <= 1'b0;
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0 <= 1'b0;
    end
    else if ( and_272_cse ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1 <= MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_3_1_1,
          lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1_mx1, and_dcpl_25);
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0 <= MUX_s_1_2_2(VCOL_else_5_if_for_and_14_ssc_1,
          lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0_mx1, and_dcpl_25);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 <= 1'b0;
    end
    else if ( rst ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 <= 1'b0;
    end
    else if ( run_wen & (((and_dcpl_4 | (~ VCOL_stage_0_1)) & VCOL_stage_0_2 & (fsm_output[1]))
        | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_mx0c1) ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 <= MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0,
          VCOL_else_5_if_for_equal_tmp_mx0w1, lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_mx0c1);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      exitL_exitL_exit_VCOL_else_5_if_for_1_sva <= 1'b0;
      VCOL_stage_0_1 <= 1'b0;
      VCOL_stage_0_2 <= 1'b0;
      ctrl_signal_triosy_obj_iswt0 <= 1'b0;
      reg_line_buf1_rsci_cgo_ir_cse <= 1'b0;
      reg_line_buf0_rsci_cgo_ir_cse <= 1'b0;
      reg_dat_out_rsci_iswt0_cse <= 1'b0;
      reg_dat_in_rsci_iswt0_cse <= 1'b0;
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1 <= 1'b0;
    end
    else if ( rst ) begin
      exitL_exitL_exit_VCOL_else_5_if_for_1_sva <= 1'b0;
      VCOL_stage_0_1 <= 1'b0;
      VCOL_stage_0_2 <= 1'b0;
      ctrl_signal_triosy_obj_iswt0 <= 1'b0;
      reg_line_buf1_rsci_cgo_ir_cse <= 1'b0;
      reg_line_buf0_rsci_cgo_ir_cse <= 1'b0;
      reg_dat_out_rsci_iswt0_cse <= 1'b0;
      reg_dat_in_rsci_iswt0_cse <= 1'b0;
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1 <= 1'b0;
    end
    else if ( run_wen ) begin
      exitL_exitL_exit_VCOL_else_5_if_for_1_sva <= mux_256_cse | VROW_y_or_cse;
      VCOL_stage_0_1 <= VCOL_aelse_VCOL_aelse_and_cse | VROW_y_or_cse;
      VCOL_stage_0_2 <= VCOL_aelse_VCOL_aelse_and_cse & (~ VROW_y_or_cse);
      ctrl_signal_triosy_obj_iswt0 <= VROW_equal_tmp & (fsm_output[2]);
      reg_line_buf1_rsci_cgo_ir_cse <= and_131_rmff;
      reg_line_buf0_rsci_cgo_ir_cse <= and_133_rmff;
      reg_dat_out_rsci_iswt0_cse <= VCOL_x_and_cse & VCOL_if_6_VCOL_if_6_and_itm_1
          & (fsm_output[1]);
      reg_dat_in_rsci_iswt0_cse <= mux_256_cse & VCOL_stage_0_1 & (~ operator_10_false_acc_itm_10_1)
          & (~ operator_11_false_acc_itm_11_1) & (fsm_output[1]);
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1 <= operator_11_false_4_operator_11_false_4_nor_tmp;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3 <= 1'b0;
    end
    else if ( rst ) begin
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3 <= 1'b0;
    end
    else if ( (~ mux_283_nl) & and_dcpl_66 & (fsm_output[1]) ) begin
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3 <= MUX1HOT_s_1_3_2(VCOL_else_5_if_for_mux_68_mx0w0,
          exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1, VCOL_VCOL_oelse_operator_11_false_or_tmp,
          {and_115_nl , and_117_nl , and_119_nl});
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_else_3_else_asn_itm_1 <= 10'b0000000000;
    end
    else if ( rst ) begin
      VCOL_else_3_else_asn_itm_1 <= 10'b0000000000;
    end
    else if ( run_wen & mux_262_cse & and_dcpl_1 ) begin
      VCOL_else_3_else_asn_itm_1 <= VROW_y_sva;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1 <= 1'b0;
    end
    else if ( rst ) begin
      operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1 <= 1'b0;
    end
    else if ( run_wen & (~ mux_tmp_8) & and_dcpl_1 ) begin
      operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1 <= VCOL_x_sva_mx1[0];
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 <= 1'b0;
      exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 <= 1'b0;
      VCOL_land_1_lpi_3_dfm_1 <= 1'b0;
      reg_i_1_lpi_3_dfm_1_cse <= 4'b0000;
      VCOL_equal_tmp_1_1 <= 1'b0;
      VCOL_equal_tmp_1 <= 1'b0;
      VCOL_equal_tmp_3_1 <= 1'b0;
      VCOL_equal_tmp_2_1 <= 1'b0;
      VCOL_land_lpi_3_dfm_1 <= 1'b0;
      max_i_3_lpi_3_dfm_1_1 <= 1'b0;
      VCOL_else_5_else_if_for_1_for_not_mdf_sva_1 <= 1'b0;
    end
    else if ( rst ) begin
      operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 <= 1'b0;
      exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 <= 1'b0;
      VCOL_land_1_lpi_3_dfm_1 <= 1'b0;
      reg_i_1_lpi_3_dfm_1_cse <= 4'b0000;
      VCOL_equal_tmp_1_1 <= 1'b0;
      VCOL_equal_tmp_1 <= 1'b0;
      VCOL_equal_tmp_3_1 <= 1'b0;
      VCOL_equal_tmp_2_1 <= 1'b0;
      VCOL_land_lpi_3_dfm_1 <= 1'b0;
      max_i_3_lpi_3_dfm_1_1 <= 1'b0;
      VCOL_else_5_else_if_for_1_for_not_mdf_sva_1 <= 1'b0;
    end
    else if ( operator_10_false_1_and_cse ) begin
      operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 <= operator_10_false_1_operator_10_false_1_and_cse_sva_1;
      exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 <= VCOL_mux_35_nl | VCOL_equal_tmp_5
          | VCOL_equal_tmp_6;
      VCOL_land_1_lpi_3_dfm_1 <= (VCOL_x_sva_mx1[0]) & operator_11_false_1_nor_tmp
          & operator_10_false_1_operator_10_false_1_and_cse_sva_1;
      reg_i_1_lpi_3_dfm_1_cse <= i_1_lpi_3_dfm_2;
      VCOL_equal_tmp_1_1 <= (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1_mx0==2'b01);
      VCOL_equal_tmp_1 <= VCOL_equal_tmp_5;
      VCOL_equal_tmp_3_1 <= VCOL_equal_tmp_6;
      VCOL_equal_tmp_2_1 <= VCOL_equal_tmp_7;
      VCOL_land_lpi_3_dfm_1 <= ~(operator_11_false_acc_itm_11_1 | operator_10_false_acc_itm_10_1);
      max_i_3_lpi_3_dfm_1_1 <= max_i_3_lpi_3_dfm_1_1_mx0;
      VCOL_else_5_else_if_for_1_for_not_mdf_sva_1 <= ~ operator_4_false_3_acc_itm_4;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      reg_operator_11_false_6_nor_itm_1_cse <= 1'b0;
      VCOL_and_37_itm_1 <= 1'b0;
      VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1 <= 1'b0;
    end
    else if ( rst ) begin
      reg_operator_11_false_6_nor_itm_1_cse <= 1'b0;
      VCOL_and_37_itm_1 <= 1'b0;
      VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1 <= 1'b0;
    end
    else if ( operator_11_false_6_and_cse ) begin
      reg_operator_11_false_6_nor_itm_1_cse <= operator_11_false_1_nor_tmp;
      VCOL_and_37_itm_1 <= (VCOL_x_sva_mx1[0]) & (~ operator_11_false_1_nor_tmp);
      VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1 <= VCOL_VCOL_oelse_operator_11_false_or_tmp;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1 <= 1'b0;
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 <= 1'b0;
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1 <= 1'b0;
    end
    else if ( rst ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1 <= 1'b0;
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 <= 1'b0;
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1 <= 1'b0;
    end
    else if ( and_281_cse ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1 <= MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_3_1_1,
          lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1_mx1, mux_tmp_236);
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 <= MUX_s_1_2_2(VCOL_else_5_if_for_and_14_ssc_1,
          lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0_mx1, mux_tmp_236);
      exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1 <= MUX_s_1_2_2(VCOL_else_5_if_for_mux_68_mx0w0,
          exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1, mux_tmp_236);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_if_6_VCOL_if_6_and_itm_1 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_if_6_VCOL_if_6_and_itm_1 <= 1'b0;
    end
    else if ( run_wen & mux_58_nl & VCOL_stage_0_1 ) begin
      VCOL_if_6_VCOL_if_6_and_itm_1 <= operator_11_false_mux_nl & VCOL_if_6_VCOL_if_6_or_cse;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      i_1_lpi_3_dfm_1_1 <= 4'b0000;
    end
    else if ( rst ) begin
      i_1_lpi_3_dfm_1_1 <= 4'b0000;
    end
    else if ( (~ mux_291_nl) & and_dcpl_66 ) begin
      i_1_lpi_3_dfm_1_1 <= i_1_sva_1_mx0w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      i_lpi_3_dfm_2_1 <= 4'b0000;
    end
    else if ( rst ) begin
      i_lpi_3_dfm_2_1 <= 4'b0000;
    end
    else if ( run_wen & and_dcpl_16 ) begin
      i_lpi_3_dfm_2_1 <= i_sva_2;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1 <= 2'b00;
    end
    else if ( rst ) begin
      VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1 <= 2'b00;
    end
    else if ( mux_292_nl & and_dcpl_66 ) begin
      VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1 <= VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1_mx0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_VCOL_slc_pix_39_32_2_lpi_4 <= 8'b00000000;
    end
    else if ( rst ) begin
      VCOL_VCOL_slc_pix_39_32_2_lpi_4 <= 8'b00000000;
    end
    else if ( or_500_cse & exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 & (~ (fsm_output[2]))
        & run_wen & VCOL_stage_0_2 ) begin
      VCOL_VCOL_slc_pix_39_32_2_lpi_4 <= VCOL_VCOL_slc_pix_39_32_2_lpi_3_dfm_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_VCOL_slc_pix_63_56_lpi_4 <= 8'b00000000;
    end
    else if ( rst ) begin
      VCOL_VCOL_slc_pix_63_56_lpi_4 <= 8'b00000000;
    end
    else if ( run_wen & (~(or_dcpl_40 | (fsm_output[2]))) & or_dcpl_4 ) begin
      VCOL_VCOL_slc_pix_63_56_lpi_4 <= pix_4_lpi_3_dfm_1_mx0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_VCOL_slc_pix_47_40_2_lpi_4 <= 8'b00000000;
    end
    else if ( rst ) begin
      VCOL_VCOL_slc_pix_47_40_2_lpi_4 <= 8'b00000000;
    end
    else if ( VCOL_and_79_cse ) begin
      VCOL_VCOL_slc_pix_47_40_2_lpi_4 <= pix_2_lpi_3_dfm_9_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_VCOL_slc_pix_71_64_lpi_4 <= 8'b00000000;
    end
    else if ( rst ) begin
      VCOL_VCOL_slc_pix_71_64_lpi_4 <= 8'b00000000;
    end
    else if ( VCOL_and_79_cse & or_dcpl_4 ) begin
      VCOL_VCOL_slc_pix_71_64_lpi_4 <= VCOL_else_5_if_for_mux_87_cse;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_2_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_2_lpi_3 <= 8'b00000000;
    end
    else if ( ((mux_295_nl & (~ VCOL_land_1_lpi_3_dfm_1)) | VCOL_land_lpi_3_dfm_1)
        & exitL_exitL_exit_VCOL_else_5_if_for_1_sva & (fsm_output[1]) & VCOL_stage_0_2
        & run_wen ) begin
      pix_2_lpi_3 <= pix_2_lpi_3_dfm_9_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_5_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_5_lpi_3 <= 8'b00000000;
    end
    else if ( mux_299_nl & VCOL_stage_0_2 & (fsm_output[1]) & run_wen ) begin
      pix_5_lpi_3 <= MUX_v_8_2_2(pix_2_lpi_3_dfm_9_mx1w0, VCOL_else_5_if_for_mux_87_cse,
          and_169_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_0_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_0_lpi_3 <= 8'b00000000;
    end
    else if ( mux_305_nl & (fsm_output[1]) & run_wen & and_dcpl_91 ) begin
      pix_0_lpi_3 <= pix_0_lpi_3_dfm_10_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      rdbuf1_pix_lpi_3 <= 16'b0000000000000000;
      rdbuf0_pix_lpi_3 <= 16'b0000000000000000;
    end
    else if ( rst ) begin
      rdbuf1_pix_lpi_3 <= 16'b0000000000000000;
      rdbuf0_pix_lpi_3 <= 16'b0000000000000000;
    end
    else if ( rdbuf1_pix_and_1_cse ) begin
      rdbuf1_pix_lpi_3 <= line_buf1_rsci_q_d;
      rdbuf0_pix_lpi_3 <= line_buf0_rsci_q_d;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_7_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_7_lpi_3 <= 8'b00000000;
    end
    else if ( mux_317_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_7_lpi_3 <= MUX_v_8_2_2(pix_4_lpi_3_dfm_1_mx0, pix_7_lpi_3_dfm_5_mx0, and_dcpl_51);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_6_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_6_lpi_3 <= 8'b00000000;
    end
    else if ( mux_329_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_6_lpi_3 <= MUX_v_8_2_2(pix_3_lpi_3_dfm_11, pix_6_lpi_3_dfm_9, and_dcpl_51);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_8_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_8_lpi_3 <= 8'b00000000;
    end
    else if ( mux_341_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_8_lpi_3 <= MUX_v_8_2_2(VCOL_else_5_if_for_mux_87_cse, pix_8_lpi_3_dfm_8,
          and_dcpl_51);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_3_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_3_lpi_3 <= 8'b00000000;
    end
    else if ( mux_350_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_3_lpi_3 <= MUX_v_8_2_2(pix_0_lpi_3_dfm_10_mx1w0, pix_3_lpi_3_dfm_11, and_dcpl_53);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_4_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_4_lpi_3 <= 8'b00000000;
    end
    else if ( mux_360_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_4_lpi_3 <= MUX_v_8_2_2(pix_1_lpi_3_dfm_10_mx1w0, pix_4_lpi_3_dfm_1_mx0,
          and_dcpl_53);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_1_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_1_lpi_3 <= 8'b00000000;
    end
    else if ( mux_365_nl & (fsm_output[1]) & run_wen & and_dcpl_91 ) begin
      pix_1_lpi_3 <= pix_1_lpi_3_dfm_10_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_result_11_lpi_3 <= 1'b0;
      pix_result_0_lpi_3 <= 1'b0;
    end
    else if ( rst ) begin
      pix_result_11_lpi_3 <= 1'b0;
      pix_result_0_lpi_3 <= 1'b0;
    end
    else if ( pix_result_and_cse ) begin
      pix_result_11_lpi_3 <= pix_result_11_lpi_3_dfm_3_mx1w0;
      pix_result_0_lpi_3 <= pix_result_0_lpi_3_dfm_3_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( rst ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( run_wen & (~ mux_40_nl) & VCOL_stage_0_1 ) begin
      lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 <= MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_0_mx0w1,
          lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_mx0w0, mux_249_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_result_10_3_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_result_10_3_lpi_3 <= 8'b00000000;
    end
    else if ( mux_368_nl & (fsm_output[1]) & VCOL_stage_0_2 & run_wen ) begin
      pix_result_10_3_lpi_3 <= pix_result_10_3_lpi_3_dfm_3_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_result_2_1_lpi_3 <= 2'b00;
    end
    else if ( rst ) begin
      pix_result_2_1_lpi_3 <= 2'b00;
    end
    else if ( mux_371_nl & (fsm_output[1]) & VCOL_stage_0_2 & run_wen ) begin
      pix_result_2_1_lpi_3 <= pix_result_2_1_lpi_3_dfm_3_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1 <= 1'b0;
    end
    else if ( rst ) begin
      exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1 <= 1'b0;
    end
    else if ( run_wen & mux_49_nl & VCOL_stage_0_1 ) begin
      exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_1_1 <= exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_2;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( rst ) begin
      operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( run_wen & mux_263_itm ) begin
      operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1 <= operator_11_false_4_operator_11_false_4_nor_tmp;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      reg_max_val_10_3_lpi_3_dfm_1_1_cse <= 8'b00000000;
    end
    else if ( rst ) begin
      reg_max_val_10_3_lpi_3_dfm_1_1_cse <= 8'b00000000;
    end
    else if ( mux_374_nl & and_dcpl_66 & or_593_cse ) begin
      reg_max_val_10_3_lpi_3_dfm_1_1_cse <= MUX_v_8_2_2(max_val_10_3_lpi_3_dfm_mx0,
          operator_12_9_false_AC_TRN_AC_SAT_8_false_slc_tmp_pix_8_7_0_cse_sva_1,
          operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_1_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_1_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_389_nl) & (fsm_output[1]) & run_wen & and_dcpl_123 ) begin
      tmp_pix_1_lpi_3 <= tmp_pix_1_lpi_3_dfm_2_mx2w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_5_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_5_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_404_nl) & (fsm_output[1]) & run_wen & and_dcpl_123 ) begin
      tmp_pix_5_lpi_3 <= tmp_pix_5_lpi_3_dfm_2_mx2w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_2_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_2_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_418_nl) & (fsm_output[1]) & run_wen & and_dcpl_123 ) begin
      tmp_pix_2_lpi_3 <= tmp_pix_2_lpi_3_dfm_2_mx2w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_6_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_6_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_432_nl) & (fsm_output[1]) & run_wen & and_dcpl_123 ) begin
      tmp_pix_6_lpi_3 <= tmp_pix_6_lpi_3_dfm_2_mx2w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_3_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_3_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_446_nl) & (fsm_output[1]) & run_wen & and_dcpl_123 ) begin
      tmp_pix_3_lpi_3 <= tmp_pix_3_lpi_3_dfm_2_mx2w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_7_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_7_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_461_nl) & (fsm_output[1]) & run_wen & and_dcpl_123 ) begin
      tmp_pix_7_lpi_3 <= tmp_pix_7_lpi_3_dfm_2_mx2w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_0_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_0_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_471_nl) & (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1==2'b10)
        & (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) & VCOL_stage_0_2 & and_dcpl_66
        & VCOL_equal_tmp_2_1 ) begin
      tmp_pix_0_lpi_3 <= tmp_pix_0_lpi_3_mx0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_8_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_8_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_483_nl) & (fsm_output[1]) & run_wen & and_dcpl_123 ) begin
      tmp_pix_8_lpi_3 <= tmp_pix_8_lpi_3_dfm_2_mx2w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      tmp_pix_4_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      tmp_pix_4_lpi_3 <= 8'b00000000;
    end
    else if ( (~ mux_497_nl) & (fsm_output[1]) & run_wen & and_dcpl_123 ) begin
      tmp_pix_4_lpi_3 <= tmp_pix_4_lpi_3_dfm_2_mx2w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1 <= 8'b00000000;
    end
    else if ( rst ) begin
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1 <= 8'b00000000;
    end
    else if ( mux_501_nl & and_dcpl_66 & (~ operator_4_false_3_acc_itm_4) ) begin
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_1 <= MUX_v_8_2_2(VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_2_1,
          VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_sva_1, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      max_i_2_0_lpi_3_dfm_1_1_2_1 <= 2'b00;
      max_i_2_0_lpi_3_dfm_1_1_0 <= 1'b0;
    end
    else if ( rst ) begin
      max_i_2_0_lpi_3_dfm_1_1_2_1 <= 2'b00;
      max_i_2_0_lpi_3_dfm_1_1_0 <= 1'b0;
    end
    else if ( and_384_cse ) begin
      max_i_2_0_lpi_3_dfm_1_1_2_1 <= MUX_v_2_2_2(j_2_0_lpi_3_dfm_3_1_rsp_0, (i_lpi_3_dfm_mx0_2_0[2:1]),
          operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
      max_i_2_0_lpi_3_dfm_1_1_0 <= MUX_s_1_2_2(j_2_0_lpi_3_dfm_3_1_rsp_1, (i_lpi_3_dfm_mx0_2_0[0]),
          operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      max_i_3_lpi_3_dfm_3_1 <= 1'b0;
    end
    else if ( rst ) begin
      max_i_3_lpi_3_dfm_3_1 <= 1'b0;
    end
    else if ( (~((~(lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1 & (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1==2'b10)
        & (~(exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0))))
        & VCOL_stage_0_2)) & and_dcpl_66 ) begin
      max_i_3_lpi_3_dfm_3_1 <= MUX_s_1_2_2(VCOL_else_5_if_for_mux_85_nl, max_i_3_lpi_3_mx1,
          mux_tmp_236);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_2_1 <= 8'b00000000;
    end
    else if ( rst ) begin
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_2_1 <= 8'b00000000;
    end
    else if ( run_wen & exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1 & and_dcpl_16
        ) begin
      VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_lpi_3_dfm_2_1 <= VCOL_else_5_else_if_for_1_slc_tmp_pix_8_7_0_cse_sva_1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      j_2_0_lpi_3_dfm_3_1_rsp_0 <= 2'b00;
    end
    else if ( rst ) begin
      j_2_0_lpi_3_dfm_3_1_rsp_0 <= 2'b00;
    end
    else if ( run_wen & (exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_mx1 | j_and_1_rgt
        | j_2_0_lpi_3_dfm_3_1_mx1c3 | (~ (fsm_output[1]))) ) begin
      j_2_0_lpi_3_dfm_3_1_rsp_0 <= MUX_v_2_2_2(({{1{operator_4_false_acc_itm_3}},
          operator_4_false_acc_itm_3}), (operator_4_false_acc_psp_sva_1[2:1]), j_or_1_itm);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      j_2_0_lpi_3_dfm_3_1_rsp_1 <= 1'b0;
    end
    else if ( rst ) begin
      j_2_0_lpi_3_dfm_3_1_rsp_1 <= 1'b0;
    end
    else if ( (~((~((~ mux_509_nl) & VCOL_stage_0_1)) & (fsm_output[1]))) & run_wen
        ) begin
      j_2_0_lpi_3_dfm_3_1_rsp_1 <= MUX_s_1_2_2(j_2_0_lpi_3_dfm_3_1_mx0w0_0, j_mux1h_2_nl,
          fsm_output[1]);
    end
  end
  assign not_687_nl = ~ VROW_y_or_cse;
  assign VROW_y_not_2_nl = ~ (fsm_output[0]);
  assign nl_operator_12_9_false_AC_TRN_AC_SAT_acc_nl = ({1'b1 , (~ pix_result_11_lpi_3_dfm_3_mx1w0)
      , (~ pix_result_10_3_lpi_3_dfm_3_mx1w0) , (~ pix_result_2_1_lpi_3_dfm_3_mx1w0)
      , (~ pix_result_0_lpi_3_dfm_3_mx1w0)}) + 13'b0011111111001;
  assign operator_12_9_false_AC_TRN_AC_SAT_acc_nl = nl_operator_12_9_false_AC_TRN_AC_SAT_acc_nl[12:0];
  assign and_115_nl = mux_372_cse & exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_2 & VCOL_stage_0_1
      & (fsm_output[1]);
  assign mux_222_nl = MUX_s_1_2_2(or_774_cse, mux_36_cse, operator_4_false_acc_itm_3);
  assign mux_223_nl = MUX_s_1_2_2(mux_222_nl, nor_85_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_227_nl = MUX_s_1_2_2(mux_231_cse, mux_223_nl, VCOL_stage_0_2);
  assign and_117_nl = mux_227_nl & VCOL_stage_0_1 & (fsm_output[1]);
  assign and_251_nl = exitL_exitL_exit_VCOL_else_5_if_for_1_sva & (~ mux_231_cse);
  assign nor_111_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1_mx0w0 |
      mux_231_cse);
  assign mux_228_nl = MUX_s_1_2_2(and_251_nl, nor_111_nl, VCOL_stage_0_2);
  assign and_119_nl = mux_228_nl & VCOL_stage_0_1 & (fsm_output[1]);
  assign or_480_nl = (~ lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3) | (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1)
      | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0 | operator_4_false_2_acc_itm_2
      | operator_4_false_3_acc_itm_4;
  assign mux_282_nl = MUX_s_1_2_2(or_480_nl, mux_231_cse, exitL_exitL_exit_VCOL_else_5_if_for_1_sva);
  assign and_nl = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) & or_479_cse;
  assign nor_246_nl = ~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) | (~
      operator_4_false_acc_itm_3));
  assign mux_279_nl = MUX_s_1_2_2(and_nl, nor_246_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign mux_280_nl = MUX_s_1_2_2(mux_279_nl, VCOL_else_4_else_aif_equal_tmp, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_283_nl = MUX_s_1_2_2(mux_282_nl, mux_280_nl, VCOL_stage_0_2);
  assign VCOL_else_5_if_for_VCOL_else_5_if_for_nor_nl = ~(lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_3_1_1
      | VCOL_else_5_if_for_and_14_ssc_1);
  assign VCOL_mux_35_nl = MUX_s_1_2_2((~ operator_4_false_acc_itm_3), VCOL_else_5_if_for_VCOL_else_5_if_for_nor_nl,
      VCOL_equal_tmp_7);
  assign operator_11_false_mux_nl = MUX_s_1_2_2(exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3,
      VCOL_VCOL_oelse_operator_11_false_or_tmp, mux_263_itm);
  assign mux_57_nl = MUX_s_1_2_2((~ operator_4_false_acc_itm_3), mux_231_cse, or_72_cse);
  assign nand_57_nl = ~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) & or_479_cse);
  assign mux_229_nl = MUX_s_1_2_2(nand_57_nl, or_325_cse, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign mux_55_nl = MUX_s_1_2_2(mux_229_nl, nor_85_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_58_nl = MUX_s_1_2_2(mux_57_nl, mux_55_nl, VCOL_stage_0_2);
  assign nand_108_nl = ~(((~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0
      | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10) | (ctrl_signal_rsci_idat[0]))
      & operator_4_false_acc_itm_3);
  assign mux_290_nl = MUX_s_1_2_2(nand_108_nl, mux_231_cse, or_72_cse);
  assign nand_109_nl = ~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) & or_495_cse);
  assign mux_288_nl = MUX_s_1_2_2(nand_109_nl, or_325_cse, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign or_493_nl = VCOL_else_4_else_aif_equal_tmp | mux_231_cse;
  assign mux_289_nl = MUX_s_1_2_2(mux_288_nl, or_493_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_291_nl = MUX_s_1_2_2(mux_290_nl, mux_289_nl, VCOL_stage_0_2);
  assign nor_255_nl = ~(VCOL_else_4_else_aif_equal_tmp | (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1));
  assign mux_292_nl = MUX_s_1_2_2(or_72_cse, nor_255_nl, VCOL_stage_0_2);
  assign mux_293_nl = MUX_s_1_2_2(and_396_cse, VCOL_else_4_else_aif_equal_tmp, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign or_503_nl = and_397_cse | VROW_equal_tmp;
  assign mux_294_nl = MUX_s_1_2_2(mux_293_nl, or_503_nl, reg_operator_11_false_6_nor_itm_1_cse);
  assign or_502_nl = VCOL_else_4_else_aif_equal_tmp | VROW_equal_tmp;
  assign mux_295_nl = MUX_s_1_2_2(mux_294_nl, or_502_nl, or_501_cse);
  assign and_169_nl = and_dcpl_51 & (fsm_output[1]);
  assign nor_256_nl = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 |
      (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) | (VCOL_x_sva!=11'b00000000001));
  assign mux_297_nl = MUX_s_1_2_2(exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1, nor_256_nl,
      VCOL_else_4_else_aif_equal_tmp);
  assign or_507_nl = exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 | reg_operator_11_false_6_nor_itm_1_cse
      | (VCOL_x_sva!=11'b00000000001);
  assign nand_66_nl = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 &
      nand_110_cse);
  assign mux_296_nl = MUX_s_1_2_2(or_507_nl, nand_66_nl, VCOL_else_4_else_aif_equal_tmp);
  assign mux_298_nl = MUX_s_1_2_2(mux_297_nl, mux_296_nl, VROW_equal_tmp);
  assign or_505_nl = (~ exitL_exitL_exit_VCOL_else_5_if_for_1_sva) | VCOL_land_1_lpi_3_dfm_1;
  assign mux_299_nl = MUX_s_1_2_2(mux_298_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1,
      or_505_nl);
  assign and_400_nl = nand_112_cse & mux_tmp_299;
  assign mux_304_nl = MUX_s_1_2_2(and_400_nl, nand_tmp_18, VCOL_else_4_else_aif_equal_tmp);
  assign mux_303_nl = MUX_s_1_2_2(mux_tmp_299, nand_tmp_18, VCOL_else_4_else_aif_equal_tmp);
  assign nor_145_nl = ~((~((VROW_y_sva!=10'b0000000001))) | (VCOL_x_sva_2!=11'b00000000001));
  assign mux_305_nl = MUX_s_1_2_2(mux_304_nl, mux_303_nl, nor_145_nl);
  assign nor_258_nl = ~(VCOL_stage_0_1 | (~ mux_tmp_309));
  assign and_402_nl = nand_114_cse & mux_tmp_309;
  assign mux_313_nl = MUX_s_1_2_2(and_402_nl, mux_tmp_309, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_314_nl = MUX_s_1_2_2(nor_258_nl, mux_313_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign and_407_nl = nand_116_cse & mux_tmp_309;
  assign mux_315_nl = MUX_s_1_2_2(mux_314_nl, and_407_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign nor_259_nl = ~(VCOL_stage_0_1 | (~ VCOL_or_tmp_1));
  assign and_405_nl = nand_114_cse & VCOL_or_tmp_1;
  assign mux_308_nl = MUX_s_1_2_2(and_405_nl, VCOL_or_tmp_1, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_309_nl = MUX_s_1_2_2(nor_259_nl, mux_308_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign and_408_nl = nand_116_cse & VCOL_or_tmp_1;
  assign mux_310_nl = MUX_s_1_2_2(mux_309_nl, and_408_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign mux_316_nl = MUX_s_1_2_2(mux_315_nl, mux_310_nl, or_522_cse);
  assign and_409_nl = exitL_exitL_exit_VCOL_else_5_if_for_1_sva & mux_316_nl;
  assign mux_317_nl = MUX_s_1_2_2(and_409_nl, mux_307_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign nor_260_nl = ~(VCOL_stage_0_1 | (~ mux_tmp_321));
  assign and_411_nl = nand_114_cse & mux_tmp_321;
  assign mux_325_nl = MUX_s_1_2_2(and_411_nl, mux_tmp_321, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_326_nl = MUX_s_1_2_2(nor_260_nl, mux_325_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign and_416_nl = nand_116_cse & mux_tmp_321;
  assign mux_327_nl = MUX_s_1_2_2(mux_326_nl, and_416_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign nor_261_nl = ~(VCOL_stage_0_1 | (~ mux_tmp_317));
  assign and_414_nl = nand_114_cse & mux_tmp_317;
  assign mux_321_nl = MUX_s_1_2_2(and_414_nl, mux_tmp_317, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_322_nl = MUX_s_1_2_2(nor_261_nl, mux_321_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign and_417_nl = nand_116_cse & mux_tmp_317;
  assign mux_323_nl = MUX_s_1_2_2(mux_322_nl, and_417_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign mux_328_nl = MUX_s_1_2_2(mux_327_nl, mux_323_nl, or_522_cse);
  assign and_418_nl = exitL_exitL_exit_VCOL_else_5_if_for_1_sva & mux_328_nl;
  assign mux_329_nl = MUX_s_1_2_2(and_418_nl, mux_307_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign nor_262_nl = ~(VCOL_stage_0_1 | (~ mux_tmp_333));
  assign and_420_nl = nand_114_cse & mux_tmp_333;
  assign mux_337_nl = MUX_s_1_2_2(and_420_nl, mux_tmp_333, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_338_nl = MUX_s_1_2_2(nor_262_nl, mux_337_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign and_425_nl = nand_116_cse & mux_tmp_333;
  assign mux_339_nl = MUX_s_1_2_2(mux_338_nl, and_425_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign nor_263_nl = ~(VCOL_stage_0_1 | (~ mux_tmp_329));
  assign and_423_nl = nand_114_cse & mux_tmp_329;
  assign mux_333_nl = MUX_s_1_2_2(and_423_nl, mux_tmp_329, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_334_nl = MUX_s_1_2_2(nor_263_nl, mux_333_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign and_426_nl = nand_116_cse & mux_tmp_329;
  assign mux_335_nl = MUX_s_1_2_2(mux_334_nl, and_426_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign mux_340_nl = MUX_s_1_2_2(mux_339_nl, mux_335_nl, or_522_cse);
  assign and_427_nl = exitL_exitL_exit_VCOL_else_5_if_for_1_sva & mux_340_nl;
  assign mux_341_nl = MUX_s_1_2_2(and_427_nl, mux_307_cse, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign nor_264_nl = ~((~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) | operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1
      | not_tmp_287);
  assign nor_265_nl = ~((~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1) | operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1);
  assign mux_349_nl = MUX_s_1_2_2(nor_264_nl, nor_265_nl, VCOL_else_4_else_aif_equal_tmp);
  assign or_572_nl = (~ operator_10_false_1_operator_10_false_1_and_cse_sva_1_1)
      | VROW_equal_tmp | (~(or_501_cse & (VCOL_x_sva_2[0]) & or_tmp_477));
  assign or_567_nl = (~ VCOL_stage_0_1) | (VCOL_x_sva_2[10:1]!=10'b0000000000);
  assign mux_344_nl = MUX_s_1_2_2(or_572_nl, or_tmp_484, or_567_nl);
  assign mux_345_nl = MUX_s_1_2_2(not_tmp_287, mux_344_nl, operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1);
  assign mux_346_nl = MUX_s_1_2_2(or_tmp_484, mux_345_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_342_nl = MUX_s_1_2_2(not_tmp_284, and_429_cse, VROW_equal_tmp);
  assign nor_267_nl = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 |
      mux_342_nl);
  assign nand_73_nl = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 &
      (~(VROW_equal_tmp & (VCOL_x_sva[0]) & reg_operator_11_false_6_nor_itm_1_cse)));
  assign mux_343_nl = MUX_s_1_2_2(nor_267_nl, nand_73_nl, or_564_cse);
  assign mux_347_nl = MUX_s_1_2_2(mux_346_nl, mux_343_nl, VCOL_else_4_else_aif_equal_tmp);
  assign or_563_nl = VCOL_else_4_else_aif_equal_tmp | (~ exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1)
      | (~ VCOL_stage_0_1) | (VCOL_x_sva_2[10:1]!=10'b0000000000) | and_tmp_25;
  assign or_560_nl = VCOL_land_1_lpi_3_dfm_1 | operator_11_false_4_operator_11_false_4_nor_cse_sva_1;
  assign mux_348_nl = MUX_s_1_2_2((~ mux_347_nl), or_563_nl, or_560_nl);
  assign mux_350_nl = MUX_s_1_2_2(mux_349_nl, mux_348_nl, exitL_exitL_exit_VCOL_else_5_if_for_1_sva);
  assign and_323_nl = ((~ VCOL_stage_0_1) | (VCOL_x_sva_2!=11'b00000000000)) & nand_tmp_25;
  assign mux_354_nl = MUX_s_1_2_2(nand_tmp_25, mux_tmp_348, or_522_cse);
  assign mux_353_nl = MUX_s_1_2_2(mux_tmp_348, nand_tmp_25, reg_operator_11_false_6_nor_itm_1_cse);
  assign mux_355_nl = MUX_s_1_2_2(mux_354_nl, mux_353_nl, VROW_equal_tmp);
  assign mux_356_nl = MUX_s_1_2_2(mux_tmp_348, mux_355_nl, VCOL_x_sva[0]);
  assign mux_352_nl = MUX_s_1_2_2(mux_tmp_348, nand_tmp_25, and_431_cse);
  assign mux_357_nl = MUX_s_1_2_2(mux_356_nl, mux_352_nl, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign mux_358_nl = MUX_s_1_2_2(mux_357_nl, nand_tmp_25, VCOL_land_1_lpi_3_dfm_1);
  assign mux_359_nl = MUX_s_1_2_2(and_323_nl, mux_358_nl, VCOL_else_4_else_aif_equal_tmp);
  assign mux_360_nl = MUX_s_1_2_2(VCOL_else_5_if_for_and_6_cse, mux_359_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_363_nl = MUX_s_1_2_2(or_tmp_501, (~ or_tmp_497), VCOL_x_sva_2[0]);
  assign or_585_nl = (VCOL_x_sva_2[10:1]!=10'b0000000000);
  assign mux_364_nl = MUX_s_1_2_2(mux_363_nl, or_tmp_501, or_585_nl);
  assign or_584_nl = (VCOL_x_sva!=11'b00000000001) | operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_and_37_itm_1;
  assign or_583_nl = (~ (VCOL_x_sva[0])) | (~ reg_operator_11_false_6_nor_itm_1_cse)
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_and_37_itm_1;
  assign mux_361_nl = MUX_s_1_2_2(or_584_nl, or_583_nl, VROW_equal_tmp);
  assign mux_362_nl = MUX_s_1_2_2(mux_361_nl, or_tmp_497, VCOL_land_1_lpi_3_dfm_1);
  assign mux_365_nl = MUX_s_1_2_2((~ mux_364_nl), mux_362_nl, VCOL_else_4_else_aif_equal_tmp);
  assign mux_247_nl = MUX_s_1_2_2((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]),
      (ctrl_signal_rsci_idat[0]), exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_249_nl = MUX_s_1_2_2((ctrl_signal_rsci_idat[0]), mux_247_nl, VCOL_stage_0_2);
  assign or_52_nl = VCOL_else_4_else_aif_equal_tmp | mux_tmp_16;
  assign mux_37_nl = MUX_s_1_2_2(mux_36_cse, or_52_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_40_nl = MUX_s_1_2_2(mux_tmp_16, mux_37_nl, VCOL_stage_0_2);
  assign mux_367_nl = MUX_s_1_2_2(not_tmp_297, or_tmp_504, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign mux_366_nl = MUX_s_1_2_2(not_tmp_297, or_tmp_504, or_587_cse);
  assign mux_368_nl = MUX_s_1_2_2(mux_367_nl, mux_366_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign and_335_nl = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]) & or_tmp_507;
  assign and_334_nl = or_587_cse & or_tmp_507;
  assign mux_370_nl = MUX_s_1_2_2(and_335_nl, and_334_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_371_nl = MUX_s_1_2_2(or_tmp_507, mux_370_nl, VCOL_stage_0_1);
  assign nor_79_nl = ~((~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0);
  assign mux_48_nl = MUX_s_1_2_2(or_tmp_41, nor_79_nl, nor_16_cse);
  assign or_438_nl = (~((~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1) |
      lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0)) | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10);
  assign nor_82_nl = ~(VCOL_else_4_else_aif_equal_tmp | (~ or_tmp_41));
  assign mux_47_nl = MUX_s_1_2_2(or_438_nl, nor_82_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_49_nl = MUX_s_1_2_2(mux_48_nl, mux_47_nl, VCOL_stage_0_2);
  assign mux_374_nl = MUX_s_1_2_2(mux_242_cse, mux_372_cse, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign or_783_nl = nor_272_cse | mux_tmp_373;
  assign mux_385_nl = MUX_s_1_2_2(mux_tmp_378, or_783_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_386_nl = MUX_s_1_2_2(nand_tmp_28, mux_385_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign mux_387_nl = MUX_s_1_2_2(mux_386_nl, mux_tmp_373, or_612_cse);
  assign or_611_nl = operator_4_false_acc_itm_3 | nand_tmp_28;
  assign or_609_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | mux_tmp_378;
  assign mux_382_nl = MUX_s_1_2_2(or_611_nl, or_609_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_604_nl = nor_187_cse | mux_tmp_373;
  assign mux_383_nl = MUX_s_1_2_2(mux_382_nl, or_604_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign or_603_nl = nor_186_cse | mux_tmp_373;
  assign mux_384_nl = MUX_s_1_2_2(mux_383_nl, or_603_nl, or_774_cse);
  assign nor_185_nl = ~((i_1_sva_1_mx0w0!=4'b0001));
  assign mux_388_nl = MUX_s_1_2_2(mux_387_nl, mux_384_nl, nor_185_nl);
  assign mux_389_nl = MUX_s_1_2_2(mux_tmp_373, mux_388_nl, VCOL_stage_0_1);
  assign or_629_nl = nor_196_cse | mux_tmp_388;
  assign mux_400_nl = MUX_s_1_2_2(mux_tmp_393, or_629_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_401_nl = MUX_s_1_2_2(or_tmp_540, mux_400_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign mux_402_nl = MUX_s_1_2_2(mux_401_nl, mux_tmp_388, or_612_cse);
  assign or_627_nl = operator_4_false_acc_itm_3 | or_tmp_540;
  assign or_625_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | mux_tmp_393;
  assign mux_397_nl = MUX_s_1_2_2(or_627_nl, or_625_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_620_nl = nor_187_cse | mux_tmp_388;
  assign mux_398_nl = MUX_s_1_2_2(mux_397_nl, or_620_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign or_619_nl = nor_186_cse | mux_tmp_388;
  assign mux_399_nl = MUX_s_1_2_2(mux_398_nl, or_619_nl, or_774_cse);
  assign nor_190_nl = ~((i_1_sva_1_mx0w0!=4'b0101));
  assign mux_403_nl = MUX_s_1_2_2(mux_402_nl, mux_399_nl, nor_190_nl);
  assign mux_404_nl = MUX_s_1_2_2(mux_tmp_388, mux_403_nl, VCOL_stage_0_1);
  assign or_647_nl = operator_4_false_acc_itm_3 | nand_tmp_35;
  assign or_646_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | mux_tmp_407;
  assign mux_414_nl = MUX_s_1_2_2(or_647_nl, or_646_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_645_nl = nor_187_cse | mux_tmp_402;
  assign mux_415_nl = MUX_s_1_2_2(mux_414_nl, or_645_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign or_644_nl = nor_186_cse | mux_tmp_402;
  assign mux_416_nl = MUX_s_1_2_2(mux_415_nl, or_644_nl, or_774_cse);
  assign or_784_nl = nor_272_cse | mux_tmp_402;
  assign mux_411_nl = MUX_s_1_2_2(mux_tmp_407, or_784_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_412_nl = MUX_s_1_2_2(nand_tmp_35, mux_411_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign mux_413_nl = MUX_s_1_2_2(mux_412_nl, mux_tmp_402, or_612_cse);
  assign or_630_nl = (i_1_sva_1_mx0w0!=4'b0010);
  assign mux_417_nl = MUX_s_1_2_2(mux_416_nl, mux_413_nl, or_630_nl);
  assign mux_418_nl = MUX_s_1_2_2(mux_tmp_402, mux_417_nl, VCOL_stage_0_1);
  assign or_665_nl = operator_4_false_acc_itm_3 | or_tmp_574;
  assign or_664_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | mux_tmp_421;
  assign mux_428_nl = MUX_s_1_2_2(or_665_nl, or_664_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_663_nl = nor_187_cse | mux_tmp_416;
  assign mux_429_nl = MUX_s_1_2_2(mux_428_nl, or_663_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign or_662_nl = nor_186_cse | mux_tmp_416;
  assign mux_430_nl = MUX_s_1_2_2(mux_429_nl, or_662_nl, or_774_cse);
  assign or_654_nl = nor_196_cse | mux_tmp_416;
  assign mux_425_nl = MUX_s_1_2_2(mux_tmp_421, or_654_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_426_nl = MUX_s_1_2_2(or_tmp_574, mux_425_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign mux_427_nl = MUX_s_1_2_2(mux_426_nl, mux_tmp_416, or_612_cse);
  assign or_648_nl = (i_1_sva_1_mx0w0!=4'b0110);
  assign mux_431_nl = MUX_s_1_2_2(mux_430_nl, mux_427_nl, or_648_nl);
  assign mux_432_nl = MUX_s_1_2_2(mux_tmp_416, mux_431_nl, VCOL_stage_0_1);
  assign or_683_nl = (~((~ operator_4_false_acc_itm_3) | (i_1_sva_1_mx0w0!=4'b0011)))
      | mux_tmp_431;
  assign or_682_nl = (i_1_lpi_3_dfm_1_1[1]) | mux_tmp_431;
  assign or_681_nl = (i_1_lpi_3_dfm_1_1[1]) | (i_1_sva_1_mx0w0[0]) | mux_tmp_431;
  assign nor_213_nl = ~((~ operator_4_false_acc_itm_3) | (i_1_sva_1_mx0w0[3:1]!=3'b001));
  assign mux_441_nl = MUX_s_1_2_2(or_682_nl, or_681_nl, nor_213_nl);
  assign nor_212_nl = ~((i_1_lpi_3_dfm_1_1[3]) | (i_1_lpi_3_dfm_1_1[2]) | (~ (i_1_lpi_3_dfm_1_1[0])));
  assign mux_442_nl = MUX_s_1_2_2(or_683_nl, mux_441_nl, nor_212_nl);
  assign or_679_nl = nor_211_cse | lfst_exitL_exit_VCOL_else_5_if_for_1_lpi_3 | (reg_i_1_lpi_3_dfm_1_cse[3:2]!=2'b00)
      | not_tmp_319;
  assign mux_436_nl = MUX_s_1_2_2(or_679_nl, mux_tmp_431, max_i_3_lpi_3_dfm_3_1);
  assign or_785_nl = (~((i_lpi_3_dfm_2_1!=4'b0011))) | mux_tmp_431;
  assign mux_437_nl = MUX_s_1_2_2(mux_436_nl, or_785_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign or_676_nl = (~((j_2_0_lpi_3_dfm_3_1_rsp_0[1]) | (~ j_2_0_lpi_3_dfm_3_1_rsp_1)
      | (~ (j_2_0_lpi_3_dfm_3_1_rsp_0[0])))) | mux_tmp_431;
  assign or_675_nl = (~((operator_4_false_acc_psp_sva_1!=3'b011))) | mux_tmp_431;
  assign mux_435_nl = MUX_s_1_2_2(or_676_nl, or_675_nl, operator_12_9_false_AC_TRN_AC_SAT_8_false_acc_itm_8);
  assign mux_438_nl = MUX_s_1_2_2(mux_437_nl, mux_435_nl, exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1);
  assign mux_439_nl = MUX_s_1_2_2(mux_438_nl, mux_tmp_431, operator_4_false_3_acc_itm_4);
  assign nand_87_nl = ~(((i_1_lpi_3_dfm_1_1[3:2]!=2'b00)) & (~((~((i_1_sva_1_mx0w0!=4'b0011)))
      | mux_tmp_431)));
  assign mux_440_nl = MUX_s_1_2_2(mux_439_nl, nand_87_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_443_nl = MUX_s_1_2_2(mux_442_nl, mux_440_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign mux_444_nl = MUX_s_1_2_2(mux_443_nl, mux_tmp_431, or_774_cse);
  assign or_671_nl = (~(VCOL_else_4_else_aif_equal_tmp | (ctrl_signal_rsci_idat!=2'b10)
      | (~ operator_4_false_acc_itm_3) | (i_1_sva_1_mx0w0!=4'b0011))) | mux_tmp_431;
  assign mux_445_nl = MUX_s_1_2_2(mux_444_nl, or_671_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_446_nl = MUX_s_1_2_2(mux_tmp_431, mux_445_nl, VCOL_stage_0_1);
  assign or_698_nl = nor_196_cse | mux_tmp_445;
  assign mux_457_nl = MUX_s_1_2_2(mux_tmp_450, or_698_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_458_nl = MUX_s_1_2_2(or_tmp_609, mux_457_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign mux_459_nl = MUX_s_1_2_2(mux_458_nl, mux_tmp_445, or_612_cse);
  assign or_696_nl = operator_4_false_acc_itm_3 | or_tmp_609;
  assign or_694_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | mux_tmp_450;
  assign mux_454_nl = MUX_s_1_2_2(or_696_nl, or_694_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_689_nl = nor_187_cse | mux_tmp_445;
  assign mux_455_nl = MUX_s_1_2_2(mux_454_nl, or_689_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign or_688_nl = nor_186_cse | mux_tmp_445;
  assign mux_456_nl = MUX_s_1_2_2(mux_455_nl, or_688_nl, or_774_cse);
  assign and_434_nl = (i_1_sva_1_mx0w0==4'b0111);
  assign mux_460_nl = MUX_s_1_2_2(mux_459_nl, mux_456_nl, and_434_nl);
  assign mux_461_nl = MUX_s_1_2_2(mux_tmp_445, mux_460_nl, VCOL_stage_0_1);
  assign or_712_nl = operator_4_false_acc_itm_3 | nand_tmp_45;
  assign mux_469_nl = MUX_s_1_2_2(nand_tmp_44, mux_tmp_459, operator_4_false_3_acc_itm_4);
  assign or_711_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | mux_469_nl;
  assign mux_470_nl = MUX_s_1_2_2(or_712_nl, or_711_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_700_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | operator_4_false_3_acc_itm_4;
  assign mux_467_nl = MUX_s_1_2_2(nand_tmp_44, mux_tmp_459, or_700_nl);
  assign mux_468_nl = MUX_s_1_2_2(nand_tmp_45, mux_467_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_699_nl = (i_1_sva_1_mx0w0!=4'b0000);
  assign mux_471_nl = MUX_s_1_2_2(mux_470_nl, mux_468_nl, or_699_nl);
  assign or_732_nl = operator_4_false_acc_itm_3 | nand_tmp_46;
  assign or_730_nl = operator_4_false_3_acc_itm_4 | exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1;
  assign mux_478_nl = MUX_s_1_2_2(mux_tmp_471, mux_tmp_469, or_730_nl);
  assign or_731_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | mux_478_nl;
  assign mux_479_nl = MUX_s_1_2_2(or_732_nl, or_731_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_729_nl = nor_187_cse | mux_tmp_469;
  assign mux_480_nl = MUX_s_1_2_2(mux_479_nl, or_729_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign or_728_nl = nor_186_cse | mux_tmp_469;
  assign mux_481_nl = MUX_s_1_2_2(mux_480_nl, or_728_nl, or_774_cse);
  assign or_721_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | operator_4_false_3_acc_itm_4
      | exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1;
  assign mux_475_nl = MUX_s_1_2_2(mux_tmp_471, mux_tmp_469, or_721_nl);
  assign mux_476_nl = MUX_s_1_2_2(nand_tmp_46, mux_475_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign mux_477_nl = MUX_s_1_2_2(mux_476_nl, mux_tmp_469, or_612_cse);
  assign or_713_nl = (i_1_sva_1_mx0w0!=4'b1000);
  assign mux_482_nl = MUX_s_1_2_2(mux_481_nl, mux_477_nl, or_713_nl);
  assign mux_483_nl = MUX_s_1_2_2(mux_tmp_469, mux_482_nl, VCOL_stage_0_1);
  assign or_749_nl = operator_4_false_acc_itm_3 | or_tmp_659;
  assign or_748_nl = lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | mux_tmp_486;
  assign mux_493_nl = MUX_s_1_2_2(or_749_nl, or_748_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign or_747_nl = nor_187_cse | mux_tmp_481;
  assign mux_494_nl = MUX_s_1_2_2(mux_493_nl, or_747_nl, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign or_746_nl = nor_186_cse | mux_tmp_481;
  assign mux_495_nl = MUX_s_1_2_2(mux_494_nl, or_746_nl, or_774_cse);
  assign or_738_nl = nor_196_cse | mux_tmp_481;
  assign mux_490_nl = MUX_s_1_2_2(mux_tmp_486, or_738_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0);
  assign mux_491_nl = MUX_s_1_2_2(or_tmp_659, mux_490_nl, lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1);
  assign mux_492_nl = MUX_s_1_2_2(mux_491_nl, mux_tmp_481, or_612_cse);
  assign or_nl = (i_1_sva_1_mx0w0!=4'b0100);
  assign mux_496_nl = MUX_s_1_2_2(mux_495_nl, mux_492_nl, or_nl);
  assign mux_497_nl = MUX_s_1_2_2(mux_tmp_481, mux_496_nl, VCOL_stage_0_1);
  assign or_786_nl = (max_i_2_0_lpi_3_dfm_1_1_2_1[0]) | (~ mux_tmp_495);
  assign nand_139_nl = ~((max_i_2_0_lpi_3_dfm_1_1_2_1[0]) & mux_tmp_495);
  assign mux_499_nl = MUX_s_1_2_2(or_786_nl, nand_139_nl, j_2_0_lpi_3_dfm_3_1_rsp_0[0]);
  assign nor_277_nl = ~((max_i_2_0_lpi_3_dfm_1_1_2_1[1]) | mux_499_nl);
  assign nor_278_nl = ~((~ (max_i_2_0_lpi_3_dfm_1_1_2_1[1])) | (j_2_0_lpi_3_dfm_3_1_rsp_0[0])
      | (max_i_2_0_lpi_3_dfm_1_1_2_1[0]) | (~ mux_tmp_495));
  assign mux_500_nl = MUX_s_1_2_2(nor_277_nl, nor_278_nl, j_2_0_lpi_3_dfm_3_1_rsp_0[1]);
  assign nor_280_nl = ~(exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1 | (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1)
      | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0 | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10)
      | (exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1 & VCOL_equal_tmp_2_1
      & (~ max_i_3_lpi_3_dfm_1_1) & VCOL_else_5_else_if_for_1_for_not_mdf_sva_1 &
      mux_500_nl));
  assign mux_501_nl = MUX_s_1_2_2(nor_270_cse, nor_280_nl, VCOL_stage_0_2);
  assign VCOL_else_5_if_for_mux_85_nl = MUX_s_1_2_2(max_i_3_lpi_3_mx1, max_i_3_lpi_3_dfm_1_1_mx0,
      VCOL_else_5_if_for_equal_tmp_mx0w1);
  assign j_mux1h_2_nl = MUX1HOT_s_1_3_2(operator_4_false_acc_itm_3, (operator_4_false_acc_psp_sva_1[0]),
      j_2_0_lpi_3_dfm_3_1_mx0w0_0, {j_and_1_rgt , j_or_1_itm , j_2_0_lpi_3_dfm_3_1_mx1c3});
  assign nor_283_nl = ~(exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3 | (~((~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10)
      | (~ operator_4_false_2_acc_itm_2))) | operator_4_false_3_acc_itm_4)));
  assign or_767_nl = (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_0;
  assign mux_507_nl = MUX_s_1_2_2(nor_283_nl, or_593_cse, or_767_nl);
  assign mux_508_nl = MUX_s_1_2_2(mux_507_nl, or_tmp_41, or_72_cse);
  assign nor_285_nl = ~(exitL_exit_VCOL_else_5_else_if_for_1_for_lpi_3_dfm_4_1 |
      (~ lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_1) | lfst_exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_4_1_0
      | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10) | exitL_exit_VCOL_else_5_if_for_lpi_3_dfm_2);
  assign mux_506_nl = MUX_s_1_2_2(nor_285_nl, VCOL_else_4_else_aif_equal_tmp, exitL_exit_VCOL_else_5_if_for_1_lpi_3_dfm_1);
  assign mux_509_nl = MUX_s_1_2_2(mux_508_nl, mux_506_nl, VCOL_stage_0_2);
  assign VROW_or_2_nl = (mux_tmp & (fsm_output[1])) | or_tmp_386;
  assign VROW_VROW_mux_1_nl = MUX_v_10_2_2(VROW_y_sva, (VCOL_x_sva_mx1[10:1]), VROW_or_2_nl);
  assign nl_z_out = VROW_VROW_mux_1_nl + conv_s2u_2_10({or_tmp_386 , 1'b1});
  assign z_out = nl_z_out[9:0];

  function automatic  MUX1HOT_s_1_3_2;
    input  input_2;
    input  input_1;
    input  input_0;
    input [2:0] sel;
    reg  result;
  begin
    result = input_0 & sel[0];
    result = result | (input_1 & sel[1]);
    result = result | (input_2 & sel[2]);
    MUX1HOT_s_1_3_2 = result;
  end
  endfunction


  function automatic [7:0] MUX1HOT_v_8_3_2;
    input [7:0] input_2;
    input [7:0] input_1;
    input [7:0] input_0;
    input [2:0] sel;
    reg [7:0] result;
  begin
    result = input_0 & {8{sel[0]}};
    result = result | (input_1 & {8{sel[1]}});
    result = result | (input_2 & {8{sel[2]}});
    MUX1HOT_v_8_3_2 = result;
  end
  endfunction


  function automatic [7:0] MUX1HOT_v_8_4_2;
    input [7:0] input_3;
    input [7:0] input_2;
    input [7:0] input_1;
    input [7:0] input_0;
    input [3:0] sel;
    reg [7:0] result;
  begin
    result = input_0 & {8{sel[0]}};
    result = result | (input_1 & {8{sel[1]}});
    result = result | (input_2 & {8{sel[2]}});
    result = result | (input_3 & {8{sel[3]}});
    MUX1HOT_v_8_4_2 = result;
  end
  endfunction


  function automatic [7:0] MUX1HOT_v_8_5_2;
    input [7:0] input_4;
    input [7:0] input_3;
    input [7:0] input_2;
    input [7:0] input_1;
    input [7:0] input_0;
    input [4:0] sel;
    reg [7:0] result;
  begin
    result = input_0 & {8{sel[0]}};
    result = result | (input_1 & {8{sel[1]}});
    result = result | (input_2 & {8{sel[2]}});
    result = result | (input_3 & {8{sel[3]}});
    result = result | (input_4 & {8{sel[4]}});
    MUX1HOT_v_8_5_2 = result;
  end
  endfunction


  function automatic [7:0] MUX1HOT_v_8_7_2;
    input [7:0] input_6;
    input [7:0] input_5;
    input [7:0] input_4;
    input [7:0] input_3;
    input [7:0] input_2;
    input [7:0] input_1;
    input [7:0] input_0;
    input [6:0] sel;
    reg [7:0] result;
  begin
    result = input_0 & {8{sel[0]}};
    result = result | (input_1 & {8{sel[1]}});
    result = result | (input_2 & {8{sel[2]}});
    result = result | (input_3 & {8{sel[3]}});
    result = result | (input_4 & {8{sel[4]}});
    result = result | (input_5 & {8{sel[5]}});
    result = result | (input_6 & {8{sel[6]}});
    MUX1HOT_v_8_7_2 = result;
  end
  endfunction


  function automatic  MUX_s_1_2_2;
    input  input_0;
    input  input_1;
    input  sel;
    reg  result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_s_1_2_2 = result;
  end
  endfunction


  function automatic [9:0] MUX_v_10_2_2;
    input [9:0] input_0;
    input [9:0] input_1;
    input  sel;
    reg [9:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_10_2_2 = result;
  end
  endfunction


  function automatic [10:0] MUX_v_11_2_2;
    input [10:0] input_0;
    input [10:0] input_1;
    input  sel;
    reg [10:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_11_2_2 = result;
  end
  endfunction


  function automatic [1:0] MUX_v_2_2_2;
    input [1:0] input_0;
    input [1:0] input_1;
    input  sel;
    reg [1:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_2_2_2 = result;
  end
  endfunction


  function automatic [2:0] MUX_v_3_2_2;
    input [2:0] input_0;
    input [2:0] input_1;
    input  sel;
    reg [2:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_3_2_2 = result;
  end
  endfunction


  function automatic [2:0] MUX_v_3_9_2;
    input [2:0] input_0;
    input [2:0] input_1;
    input [2:0] input_2;
    input [2:0] input_3;
    input [2:0] input_4;
    input [2:0] input_5;
    input [2:0] input_6;
    input [2:0] input_7;
    input [2:0] input_8;
    input [3:0] sel;
    reg [2:0] result;
  begin
    case (sel)
      4'b0000 : begin
        result = input_0;
      end
      4'b0001 : begin
        result = input_1;
      end
      4'b0010 : begin
        result = input_2;
      end
      4'b0011 : begin
        result = input_3;
      end
      4'b0100 : begin
        result = input_4;
      end
      4'b0101 : begin
        result = input_5;
      end
      4'b0110 : begin
        result = input_6;
      end
      4'b0111 : begin
        result = input_7;
      end
      default : begin
        result = input_8;
      end
    endcase
    MUX_v_3_9_2 = result;
  end
  endfunction


  function automatic [3:0] MUX_v_4_2_2;
    input [3:0] input_0;
    input [3:0] input_1;
    input  sel;
    reg [3:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_4_2_2 = result;
  end
  endfunction


  function automatic [6:0] MUX_v_7_2_2;
    input [6:0] input_0;
    input [6:0] input_1;
    input  sel;
    reg [6:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_7_2_2 = result;
  end
  endfunction


  function automatic [7:0] MUX_v_8_2_2;
    input [7:0] input_0;
    input [7:0] input_1;
    input  sel;
    reg [7:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_8_2_2 = result;
  end
  endfunction


  function automatic [7:0] MUX_v_8_6_2;
    input [7:0] input_0;
    input [7:0] input_1;
    input [7:0] input_2;
    input [7:0] input_3;
    input [7:0] input_4;
    input [7:0] input_5;
    input [2:0] sel;
    reg [7:0] result;
  begin
    case (sel)
      3'b000 : begin
        result = input_0;
      end
      3'b001 : begin
        result = input_1;
      end
      3'b010 : begin
        result = input_2;
      end
      3'b011 : begin
        result = input_3;
      end
      3'b100 : begin
        result = input_4;
      end
      default : begin
        result = input_5;
      end
    endcase
    MUX_v_8_6_2 = result;
  end
  endfunction


  function automatic [7:0] MUX_v_8_9_2;
    input [7:0] input_0;
    input [7:0] input_1;
    input [7:0] input_2;
    input [7:0] input_3;
    input [7:0] input_4;
    input [7:0] input_5;
    input [7:0] input_6;
    input [7:0] input_7;
    input [7:0] input_8;
    input [3:0] sel;
    reg [7:0] result;
  begin
    case (sel)
      4'b0000 : begin
        result = input_0;
      end
      4'b0001 : begin
        result = input_1;
      end
      4'b0010 : begin
        result = input_2;
      end
      4'b0011 : begin
        result = input_3;
      end
      4'b0100 : begin
        result = input_4;
      end
      4'b0101 : begin
        result = input_5;
      end
      4'b0110 : begin
        result = input_6;
      end
      4'b0111 : begin
        result = input_7;
      end
      default : begin
        result = input_8;
      end
    endcase
    MUX_v_8_9_2 = result;
  end
  endfunction


  function automatic [8:0] readslicef_10_9_1;
    input [9:0] vector;
    reg [9:0] tmp;
  begin
    tmp = vector >> 1;
    readslicef_10_9_1 = tmp[8:0];
  end
  endfunction


  function automatic [0:0] readslicef_11_1_10;
    input [10:0] vector;
    reg [10:0] tmp;
  begin
    tmp = vector >> 10;
    readslicef_11_1_10 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_12_1_11;
    input [11:0] vector;
    reg [11:0] tmp;
  begin
    tmp = vector >> 11;
    readslicef_12_1_11 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_13_1_12;
    input [12:0] vector;
    reg [12:0] tmp;
  begin
    tmp = vector >> 12;
    readslicef_13_1_12 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_3_1_2;
    input [2:0] vector;
    reg [2:0] tmp;
  begin
    tmp = vector >> 2;
    readslicef_3_1_2 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_4_1_3;
    input [3:0] vector;
    reg [3:0] tmp;
  begin
    tmp = vector >> 3;
    readslicef_4_1_3 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_5_1_4;
    input [4:0] vector;
    reg [4:0] tmp;
  begin
    tmp = vector >> 4;
    readslicef_5_1_4 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_9_1_8;
    input [8:0] vector;
    reg [8:0] tmp;
  begin
    tmp = vector >> 8;
    readslicef_9_1_8 = tmp[0:0];
  end
  endfunction


  function automatic [1:0] signext_2_1;
    input  vector;
  begin
    signext_2_1= {{1{vector}}, vector};
  end
  endfunction


  function automatic [9:0] conv_s2u_2_10 ;
    input [1:0]  vector ;
  begin
    conv_s2u_2_10 = {{8{vector[1]}}, vector};
  end
  endfunction


  function automatic [4:0] conv_u2s_4_5 ;
    input [3:0]  vector ;
  begin
    conv_u2s_4_5 =  {1'b0, vector};
  end
  endfunction


  function automatic [8:0] conv_u2s_8_9 ;
    input [7:0]  vector ;
  begin
    conv_u2s_8_9 =  {1'b0, vector};
  end
  endfunction


  function automatic [10:0] conv_u2s_10_11 ;
    input [9:0]  vector ;
  begin
    conv_u2s_10_11 =  {1'b0, vector};
  end
  endfunction


  function automatic [11:0] conv_u2s_11_12 ;
    input [10:0]  vector ;
  begin
    conv_u2s_11_12 =  {1'b0, vector};
  end
  endfunction


  function automatic [12:0] conv_u2u_8_13 ;
    input [7:0]  vector ;
  begin
    conv_u2u_8_13 = {{5{1'b0}}, vector};
  end
  endfunction


  function automatic [12:0] conv_u2u_12_13 ;
    input [11:0]  vector ;
  begin
    conv_u2u_12_13 = {1'b0, vector};
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter_run
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter_run (
  clk, rst, arst_n, dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, widthIn, heightIn,
      dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy, ctrl_signal_triosy_lz, ctrl_signal_rsci_idat,
      line_buf0_rsci_adr_d, line_buf0_rsci_d_d, line_buf0_rsci_en_d, line_buf0_rsci_q_d,
      line_buf1_rsci_adr_d, line_buf1_rsci_d_d, line_buf1_rsci_en_d, line_buf1_rsci_q_d,
      line_buf0_rsci_we_d_pff, line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_pff,
      line_buf1_rsci_we_d_pff
);
  input clk;
  input rst;
  input arst_n;
  input [7:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input [10:0] widthIn;
  input [9:0] heightIn;
  output [7:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  output ctrl_signal_triosy_lz;
  input [1:0] ctrl_signal_rsci_idat;
  output [9:0] line_buf0_rsci_adr_d;
  output [15:0] line_buf0_rsci_d_d;
  output line_buf0_rsci_en_d;
  input [15:0] line_buf0_rsci_q_d;
  output [9:0] line_buf1_rsci_adr_d;
  output [15:0] line_buf1_rsci_d_d;
  output line_buf1_rsci_en_d;
  input [15:0] line_buf1_rsci_q_d;
  output line_buf0_rsci_we_d_pff;
  output line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_pff;
  output line_buf1_rsci_we_d_pff;


  // Interconnect Declarations
  wire run_wen;
  wire run_wten;
  wire dat_in_rsci_wen_comp;
  wire [7:0] dat_in_rsci_idat_mxwt;
  wire dat_out_rsci_wen_comp;
  reg ctrl_signal_triosy_obj_iswt0;
  reg [3:0] dat_out_rsci_idat_7_4;
  reg [2:0] dat_out_rsci_idat_3_1;
  reg dat_out_rsci_idat_0;
  wire [3:0] fsm_output;
  wire VROW_equal_tmp;
  wire VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp;
  wire operator_10_false_1_nor_tmp;
  wire operator_11_false_4_operator_11_false_4_nor_tmp;
  wire operator_11_false_1_nor_tmp;
  wire VCOL_else_2_else_else_else_nor_1_tmp;
  wire VCOL_else_2_else_aif_equal_tmp;
  wire VCOL_VCOL_oelse_operator_11_false_or_tmp;
  wire and_dcpl_1;
  wire and_dcpl_4;
  wire and_dcpl_5;
  wire or_dcpl_3;
  wire mux_tmp_3;
  wire mux_tmp_10;
  wire or_tmp_20;
  wire or_tmp_22;
  wire mux_tmp_37;
  wire or_dcpl_28;
  wire and_dcpl_23;
  wire and_dcpl_25;
  wire or_dcpl_34;
  wire nor_tmp_13;
  wire or_tmp_69;
  wire or_dcpl_40;
  wire VCOL_else_3_if_for_mux_46_tmp_0;
  wire [3:0] VCOL_VCOL_and_6_cse;
  wire VCOL_equal_tmp_6;
  wire VCOL_equal_tmp_4;
  wire VCOL_equal_tmp_7;
  wire exitL_exitL_exit_VCOL_else_3_if_for_1_sva_mx1;
  wire operator_10_false_1_operator_10_false_1_and_cse_sva_1;
  wire lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1_mx0w0;
  reg pix_result_16_lpi_3;
  wire [17:0] VCOL_else_3_else_if_acc_sat_sva_1;
  wire [18:0] nl_VCOL_else_3_else_if_acc_sat_sva_1;
  reg VCOL_equal_tmp_1_1;
  wire VCOL_or_2_cse_1;
  wire VCOL_and_15_cse_1;
  reg lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3;
  reg VCOL_equal_tmp_2_1;
  reg VCOL_equal_tmp_3_1;
  reg lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  reg [7:0] pix_result_15_8_lpi_3;
  reg [3:0] pix_result_7_4_lpi_3;
  wire [7:0] VCOL_else_3_if_for_mux_61;
  reg [3:0] i_1_lpi_3_dfm_1;
  wire [14:0] pix_result_dx_15_1_sva_2;
  wire pix_result_dx_0_sva_2;
  wire [14:0] pix_result_dy_15_1_sva_2;
  wire pix_result_dy_0_sva_2;
  reg pix_result_dy_16_lpi_3;
  reg [14:0] pix_result_dy_15_1_lpi_3;
  reg pix_result_dy_0_lpi_3;
  reg [2:0] VCOL_else_3_else_if_for_1_mux_itm_1;
  reg pix_result_dx_16_lpi_3;
  reg [14:0] pix_result_dx_15_1_lpi_3;
  reg pix_result_dx_0_lpi_3;
  wire VCOL_else_2_else_else_else_unequal_tmp_1;
  wire VCOL_or_10_tmp_1;
  reg exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  reg operator_10_false_1_operator_10_false_1_and_cse_sva_1_1;
  wire VCOL_VCOL_nor_1_m1c_1;
  reg VCOL_land_1_lpi_3_dfm_1;
  wire VCOL_else_3_if_for_and_8_m1c_1;
  wire VCOL_else_2_VCOL_else_2_nor_1_m1c_1;
  wire VCOL_VCOL_nor_5_m1c_1;
  wire VCOL_or_tmp_1;
  wire VCOL_else_2_else_else_else_and_tmp_1;
  wire VCOL_and_m1c_1;
  reg operator_11_false_4_operator_11_false_4_nor_cse_sva_1;
  wire VCOL_else_2_else_else_VCOL_else_2_else_else_nor_3_cse_1;
  wire VCOL_else_2_else_else_else_else_and_5_tmp_1;
  wire VCOL_else_2_else_else_and_3_m1c_1;
  reg VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1;
  wire VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1_mx0;
  reg operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1;
  reg exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  reg VCOL_stage_0_2;
  reg [9:0] VROW_y_sva;
  reg [10:0] VCOL_x_sva;
  reg VCOL_stage_0_1;
  reg [1:0] VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1;
  reg VCOL_if_4_VCOL_if_4_and_itm_1;
  reg [9:0] VCOL_else_1_else_asn_itm_1;
  reg operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1;
  wire [3:0] i_sva_2;
  wire [4:0] nl_i_sva_2;
  wire [7:0] pix_result_15_8_lpi_3_dfm_2_mx0w1;
  wire [10:0] VCOL_x_sva_mx1;
  reg VCOL_equal_tmp_1;
  wire [17:0] VCOL_else_3_else_if_for_1_acc_psp_1_sva_1;
  wire [18:0] nl_VCOL_else_3_else_if_for_1_acc_psp_1_sva_1;
  wire VCOL_if_4_and_cse;
  reg reg_operator_11_false_6_nor_itm_1_cse;
  wire pix_result_dy_and_cse;
  reg reg_dat_in_rsci_oswt_cse;
  reg reg_dat_out_rsci_oswt_cse;
  reg reg_line_buf0_rsci_cgo_cse;
  reg reg_line_buf1_rsci_cgo_cse;
  wire VCOL_and_38_cse;
  wire [1:0] VCOL_mux_6_cse;
  wire mux_57_cse;
  wire or_53_cse;
  wire nand_4_cse;
  wire nor_16_cse;
  wire [3:0] i_1_sva_1_mx0w0;
  wire [4:0] nl_i_1_sva_1_mx0w0;
  wire VCOL_aelse_VCOL_aelse_and_cse;
  wire mux_59_cse;
  wire VCOL_x_and_cse;
  wire and_125_rmff;
  wire and_137_rmff;
  reg [7:0] VCOL_VCOL_slc_pix_47_40_2_lpi_4;
  wire [7:0] pix_2_lpi_3_dfm_9_mx1w0;
  reg [7:0] VCOL_VCOL_slc_pix_71_64_lpi_4;
  wire [7:0] pix_5_lpi_3_dfm_6_mx1;
  reg [7:0] VCOL_VCOL_slc_pix_39_32_2_lpi_4;
  wire [7:0] VCOL_VCOL_slc_pix_39_32_2_lpi_3_dfm_mx1w0;
  reg [7:0] VCOL_VCOL_slc_pix_63_56_lpi_4;
  wire [7:0] pix_4_lpi_3_dfm_1_mx1;
  wire mux_36_itm;
  wire mux_65_itm;
  wire mux_tmp;
  wire or_tmp_129;
  wire [9:0] z_out;
  wire [10:0] nl_z_out;
  wire or_tmp_131;
  wire [17:0] z_out_1;
  wire [18:0] nl_z_out_1;
  wire [10:0] z_out_2;
  wire signed [12:0] nl_z_out_2;
  reg [7:0] pix_0_lpi_3;
  reg [7:0] pix_1_lpi_3;
  reg [7:0] pix_2_lpi_3;
  reg [15:0] rdbuf0_pix_lpi_3;
  reg [15:0] rdbuf1_pix_lpi_3;
  reg [7:0] pix_4_lpi_3;
  reg [7:0] pix_3_lpi_3;
  reg [7:0] pix_6_lpi_3;
  reg [7:0] pix_7_lpi_3;
  reg [7:0] pix_8_lpi_3;
  reg [7:0] pix_5_lpi_3;
  reg [2:0] pix_result_3_1_lpi_3;
  reg pix_result_0_lpi_3;
  reg VCOL_land_lpi_3_dfm_1;
  reg VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1;
  reg [3:0] i_lpi_3_dfm_1_1;
  reg [3:0] i_1_lpi_3_dfm_1_1;
  reg VCOL_and_10_itm_1;
  wire lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_mx0c1;
  wire [7:0] pix_0_lpi_3_dfm_9_mx1w0;
  wire [7:0] pix_1_lpi_3_dfm_9_mx1w0;
  wire [3:0] pix_result_7_4_lpi_3_dfm_2_mx0w1;
  wire lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_2;
  wire pix_result_16_lpi_3_dfm_2_mx1w0;
  wire [2:0] pix_result_3_1_lpi_3_dfm_2_mx0w1;
  wire pix_result_0_lpi_3_dfm_2_mx1w0;
  wire [3:0] i_lpi_3_dfm_2;
  wire [7:0] pix_3_lpi_3_dfm_mx0;
  wire [7:0] pix_4_lpi_3_dfm_mx0;
  wire [7:0] pix_1_lpi_3_dfm_10;
  wire VCOL_else_2_else_else_or_6_m1c_1;
  wire VCOL_else_2_else_else_and_7_m1c_1;
  wire VCOL_lor_lpi_3_dfm_1;
  wire VCOL_else_3_if_for_nor_ovfl_sva_1;
  wire VCOL_else_3_if_for_and_unfl_sva_1;
  wire [14:0] VCOL_else_3_else_if_ac_fixed_cctor_2_15_1_sva_1;
  wire [7:0] pix_3_lpi_3_dfm_11;
  wire [7:0] pix_6_lpi_3_dfm_9;
  wire [7:0] pix_8_lpi_3_dfm_8;
  wire VCOL_else_3_else_if_nor_ovfl_2_sva_1;
  wire VCOL_else_3_else_if_and_unfl_2_sva_1;
  wire VCOL_else_3_else_if_for_1_nor_ovfl_sva_1;
  wire VCOL_else_3_else_if_for_1_and_unfl_sva_1;
  wire VCOL_else_3_else_if_for_nor_ovfl_sva_1;
  wire VCOL_else_3_else_if_for_and_unfl_sva_1;
  wire [10:0] VCOL_x_sva_2;
  wire [11:0] nl_VCOL_x_sva_2;
  wire VCOL_else_2_and_3_cse_1;
  wire VCOL_else_3_if_for_and_29_cse_1;
  wire VCOL_else_3_if_for_and_31_cse_1;
  wire VCOL_else_3_if_for_and_46_m1c_1;
  wire VCOL_else_3_if_for_and_30_m1c_1;
  wire VCOL_or_8_tmp_1;
  wire VCOL_else_3_if_for_or_m1c_1;
  wire [14:0] pix_result_dx_conc_itm_15_1;
  wire [3:0] exs_tmp_1_3_0;
  wire exs_tmp_1_12;
  wire VROW_y_or_cse;
  wire operator_10_false_1_and_cse;
  wire rdbuf1_pix_and_1_cse;
  wire operator_11_false_6_and_cse;
  wire VCOL_and_41_cse;
  wire VCOL_else_3_if_for_and_52_cse;
  wire pix_result_dy_and_3_cse;
  wire or_tmp_144;
  wire nand_tmp_4;
  wire mux_tmp_79;
  wire or_tmp_156;
  wire or_tmp_165;
  wire or_tmp_169;
  wire mux_tmp_99;
  wire nand_tmp_11;
  wire mux_tmp_104;
  wire or_tmp_191;
  wire or_tmp_195;
  wire and_dcpl_74;
  wire mux_tmp_120;
  wire not_tmp_125;
  wire and_179_cse;
  wire nand_41_cse;
  wire mux_84_cse;
  wire nor_78_cse;
  wire or_226_cse;
  wire and_232_cse;
  wire or_204_cse;
  wire or_43_cse;
  wire and_cse;
  wire and_253_cse;
  wire and_268_cse;
  wire nand_37_cse;
  wire or_222_cse;
  wire nor_57_cse;
  wire VCOL_else_3_if_for_and_5_cse;
  wire nand_39_cse;
  wire or_251_cse;
  wire operator_4_false_1_acc_itm_3;
  wire operator_4_false_2_acc_itm_3;
  wire operator_11_false_acc_itm_11_1;
  wire operator_10_false_acc_itm_10_1;
  wire operator_17_17_true_AC_RND_AC_SAT_acc_itm_8_1;

  wire not_233_nl;
  wire VROW_y_not_2_nl;
  wire[3:0] VCOL_if_4_nor_1_nl;
  wire[2:0] VCOL_if_4_nor_2_nl;
  wire mux_72_nl;
  wire mux_71_nl;
  wire mux_nl;
  wire or_188_nl;
  wire or_187_nl;
  wire or_186_nl;
  wire and_83_nl;
  wire mux_76_nl;
  wire mux_75_nl;
  wire mux_74_nl;
  wire nor_74_nl;
  wire mux_73_nl;
  wire or_192_nl;
  wire nand_27_nl;
  wire or_190_nl;
  wire mux_82_nl;
  wire mux_81_nl;
  wire and_256_nl;
  wire mux_80_nl;
  wire nor_54_nl;
  wire mux_9_nl;
  wire nand_nl;
  wire mux_16_nl;
  wire mux_15_nl;
  wire or_27_nl;
  wire mux_12_nl;
  wire mux_11_nl;
  wire nor_23_nl;
  wire mux_83_nl;
  wire or_206_nl;
  wire or_205_nl;
  wire nor_nl;
  wire mux_90_nl;
  wire and_259_nl;
  wire mux_89_nl;
  wire mux_88_nl;
  wire nor_76_nl;
  wire and_258_nl;
  wire mux_96_nl;
  wire and_262_nl;
  wire mux_95_nl;
  wire mux_94_nl;
  wire nor_77_nl;
  wire and_261_nl;
  wire mux_103_nl;
  wire mux_102_nl;
  wire and_219_nl;
  wire mux_101_nl;
  wire and_218_nl;
  wire mux_100_nl;
  wire and_264_nl;
  wire mux_98_nl;
  wire or_228_nl;
  wire mux_97_nl;
  wire or_227_nl;
  wire and_265_nl;
  wire and_216_nl;
  wire mux_113_nl;
  wire mux_112_nl;
  wire and_223_nl;
  wire mux_111_nl;
  wire mux_110_nl;
  wire mux_109_nl;
  wire mux_108_nl;
  wire mux_107_nl;
  wire mux_106_nl;
  wire mux_105_nl;
  wire mux_118_nl;
  wire mux_117_nl;
  wire mux_116_nl;
  wire or_248_nl;
  wire mux_115_nl;
  wire mux_114_nl;
  wire or_247_nl;
  wire or_246_nl;
  wire mux_24_nl;
  wire mux_23_nl;
  wire mux_21_nl;
  wire nor_24_nl;
  wire mux_30_nl;
  wire mux_27_nl;
  wire mux_26_nl;
  wire or_41_nl;
  wire mux_31_nl;
  wire mux_34_nl;
  wire nor_25_nl;
  wire nor_26_nl;
  wire VCOL_mux_5_nl;
  wire mux_42_nl;
  wire mux_41_nl;
  wire mux_39_nl;
  wire mux_38_nl;
  wire or_nl;
  wire or_169_nl;
  wire nor_34_nl;
  wire mux_48_nl;
  wire mux_47_nl;
  wire mux_45_nl;
  wire mux_44_nl;
  wire nor_27_nl;
  wire nor_28_nl;
  wire nor_29_nl;
  wire mux_52_nl;
  wire mux_119_nl;
  wire nor_83_nl;
  wire mux_55_nl;
  wire mux_54_nl;
  wire or_88_nl;
  wire mux_58_nl;
  wire nand_23_nl;
  wire or_91_nl;
  wire mux_63_nl;
  wire and_51_nl;
  wire mux_62_nl;
  wire mux_61_nl;
  wire and_181_nl;
  wire or_173_nl;
  wire mux_60_nl;
  wire nand_1_nl;
  wire or_92_nl;
  wire mux_121_nl;
  wire and_269_nl;
  wire nor_84_nl;
  wire mux_124_nl;
  wire mux_123_nl;
  wire mux_122_nl;
  wire[3:0] operator_4_false_1_acc_nl;
  wire[4:0] nl_operator_4_false_1_acc_nl;
  wire[3:0] operator_4_false_2_acc_nl;
  wire[4:0] nl_operator_4_false_2_acc_nl;
  wire VCOL_else_3_if_for_or_6_nl;
  wire VCOL_else_3_if_for_or_7_nl;
  wire VCOL_else_3_if_for_or_8_nl;
  wire VCOL_else_3_if_for_or_9_nl;
  wire VCOL_else_3_if_for_and_45_nl;
  wire VCOL_else_3_if_for_nand_12_nl;
  wire VCOL_else_3_if_for_and_41_nl;
  wire VCOL_and_8_nl;
  wire VCOL_else_3_if_for_and_42_nl;
  wire VCOL_else_3_if_for_and_33_nl;
  wire VCOL_else_3_if_for_or_3_nl;
  wire VCOL_and_11_nl;
  wire VCOL_else_3_if_for_and_43_nl;
  wire VCOL_else_3_if_for_and_44_nl;
  wire[3:0] VCOL_else_3_if_for_VCOL_else_3_if_for_nor_4_nl;
  wire[3:0] VCOL_else_3_if_for_nor_6_nl;
  wire[7:0] VCOL_mux1h_11_nl;
  wire[7:0] VCOL_else_3_if_for_VCOL_else_3_if_for_nor_1_nl;
  wire[7:0] VCOL_else_3_if_for_nor_3_nl;
  wire VCOL_not_37_nl;
  wire VCOL_else_3_if_for_mux_2_nl;
  wire VCOL_mux1h_10_nl;
  wire nor_45_nl;
  wire nor_46_nl;
  wire VCOL_else_3_if_for_and_24_nl;
  wire VCOL_else_3_if_for_and_28_nl;
  wire[2:0] VCOL_else_3_if_for_VCOL_else_3_if_for_nor_nl;
  wire[2:0] VCOL_else_3_if_for_nor_2_nl;
  wire[2:0] VCOL_VCOL_and_8_nl;
  wire VCOL_else_3_if_for_VCOL_else_3_if_for_nor_2_nl;
  wire VCOL_else_3_else_if_VCOL_else_3_else_if_nor_nl;
  wire[11:0] operator_11_false_acc_nl;
  wire[12:0] nl_operator_11_false_acc_nl;
  wire[10:0] operator_10_false_acc_nl;
  wire[11:0] nl_operator_10_false_acc_nl;
  wire VCOL_VCOL_nor_7_nl;
  wire VCOL_and_31_nl;
  wire or_107_nl;
  wire mux_67_nl;
  wire nor_40_nl;
  wire mux_66_nl;
  wire or_171_nl;
  wire nor_41_nl;
  wire[8:0] operator_17_17_true_AC_RND_AC_SAT_acc_nl;
  wire[9:0] nl_operator_17_17_true_AC_RND_AC_SAT_acc_nl;
  wire[14:0] VCOL_else_3_else_if_nor_6_nl;
  wire VCOL_else_3_if_for_nand_14_nl;
  wire VCOL_else_3_if_for_and_50_nl;
  wire VCOL_else_3_if_for_and_47_nl;
  wire nand_22_nl;
  wire VCOL_else_3_if_for_nand_8_nl;
  wire VCOL_else_3_if_for_and_36_nl;
  wire VCOL_else_3_if_for_and_38_nl;
  wire VCOL_else_3_if_for_nand_6_nl;
  wire VCOL_else_3_if_for_or_4_nl;
  wire VCOL_else_2_and_13_nl;
  wire[14:0] VCOL_else_3_else_if_for_nor_2_nl;
  wire VCOL_VCOL_and_13_nl;
  wire[14:0] VCOL_VCOL_and_14_nl;
  wire VCOL_VCOL_and_15_nl;
  wire[9:0] operator_10_10_true_AC_TRN_AC_SAT_2_mul_nl;
  wire signed [11:0] nl_operator_10_10_true_AC_TRN_AC_SAT_2_mul_nl;
  wire[14:0] VCOL_else_3_else_if_for_1_nor_2_nl;
  wire[7:0] VCOL_else_3_if_for_mux_13_nl;
  wire VCOL_else_3_if_for_and_26_nl;
  wire mux_35_nl;
  wire or_48_nl;
  wire nand_7_nl;
  wire or_49_nl;
  wire mux_69_nl;
  wire mux_68_nl;
  wire nor_42_nl;
  wire VCOL_if_1_not_nl;
  wire[7:0] VCOL_else_3_if_for_mux_6_nl;
  wire[7:0] VCOL_else_3_if_for_mux_5_nl;
  wire VCOL_if_1_nor_nl;
  wire[7:0] VCOL_mux_12_nl;
  wire[7:0] VCOL_else_3_if_for_mux_7_nl;
  wire mux_64_nl;
  wire nor_48_nl;
  wire nor_49_nl;
  wire or_183_nl;
  wire mux_77_nl;
  wire nor_85_nl;
  wire nor_86_nl;
  wire or_202_nl;
  wire mux_78_nl;
  wire or_201_nl;
  wire mux_87_nl;
  wire mux_86_nl;
  wire and_270_nl;
  wire or_208_nl;
  wire mux_85_nl;
  wire nand_29_nl;
  wire mux_93_nl;
  wire or_218_nl;
  wire or_233_nl;
  wire or_231_nl;
  wire or_241_nl;
  wire nand_48_nl;
  wire or_260_nl;
  wire[9:0] VROW_VROW_mux_1_nl;
  wire VROW_or_2_nl;
  wire VCOL_else_3_if_for_mux_68_nl;
  wire VCOL_VCOL_and_18_nl;
  wire[3:0] VCOL_else_3_if_for_mux_69_nl;
  wire[7:0] VCOL_else_3_if_for_mux_70_nl;
  wire[7:0] VCOL_VCOL_and_19_nl;
  wire[2:0] VCOL_else_3_if_for_mux_71_nl;
  wire VCOL_else_3_if_for_mux_72_nl;
  wire VCOL_VCOL_and_20_nl;
  wire VCOL_else_3_if_for_mux_73_nl;
  wire[3:0] operator_10_10_true_AC_TRN_AC_SAT_mux_1_nl;
  wire[3:0] VCOL_else_3_if_for_mux_74_nl;
  wire[2:0] VCOL_else_3_else_if_for_mux_2_nl;

  // Interconnect Declarations for Component Instantiations 
  wire [7:0] nl_EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_inst_dat_out_rsci_idat;
  assign nl_EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_inst_dat_out_rsci_idat
      = {dat_out_rsci_idat_7_4 , dat_out_rsci_idat_3_1 , dat_out_rsci_idat_0};
  wire  nl_EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm_inst_VCOL_C_0_tr0;
  assign nl_EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm_inst_VCOL_C_0_tr0 = ~(VCOL_stage_0_2
      | VCOL_stage_0_1);
  EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci EdgeDetect_IP_EdgeDetect_Filter_run_dat_in_rsci_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_in_rsc_dat(dat_in_rsc_dat),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy),
      .run_wen(run_wen),
      .dat_in_rsci_oswt(reg_dat_in_rsci_oswt_cse),
      .dat_in_rsci_wen_comp(dat_in_rsci_wen_comp),
      .dat_in_rsci_idat_mxwt(dat_in_rsci_idat_mxwt)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_out_rsc_dat(dat_out_rsc_dat),
      .dat_out_rsc_vld(dat_out_rsc_vld),
      .dat_out_rsc_rdy(dat_out_rsc_rdy),
      .run_wen(run_wen),
      .dat_out_rsci_oswt(reg_dat_out_rsci_oswt_cse),
      .dat_out_rsci_wen_comp(dat_out_rsci_wen_comp),
      .dat_out_rsci_idat(nl_EdgeDetect_IP_EdgeDetect_Filter_run_dat_out_rsci_inst_dat_out_rsci_idat[7:0])
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_wait_dp EdgeDetect_IP_EdgeDetect_Filter_run_wait_dp_inst
      (
      .line_buf0_rsci_en_d(line_buf0_rsci_en_d),
      .line_buf1_rsci_en_d(line_buf1_rsci_en_d),
      .run_wen(run_wen),
      .line_buf0_rsci_cgo(reg_line_buf0_rsci_cgo_cse),
      .line_buf0_rsci_cgo_ir_unreg(and_125_rmff),
      .line_buf1_rsci_cgo(reg_line_buf1_rsci_cgo_cse),
      .line_buf1_rsci_cgo_ir_unreg(and_137_rmff)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_ctrl_signal_triosy_obj EdgeDetect_IP_EdgeDetect_Filter_run_ctrl_signal_triosy_obj_inst
      (
      .ctrl_signal_triosy_lz(ctrl_signal_triosy_lz),
      .run_wten(run_wten),
      .ctrl_signal_triosy_obj_iswt0(ctrl_signal_triosy_obj_iswt0)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_staller EdgeDetect_IP_EdgeDetect_Filter_run_staller_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .run_wten(run_wten),
      .dat_in_rsci_wen_comp(dat_in_rsci_wen_comp),
      .dat_out_rsci_wen_comp(dat_out_rsci_wen_comp)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .fsm_output(fsm_output),
      .VCOL_C_0_tr0(nl_EdgeDetect_IP_EdgeDetect_Filter_run_run_fsm_inst_VCOL_C_0_tr0),
      .VROW_C_0_tr0(VROW_equal_tmp)
    );
  assign VROW_y_or_cse = (fsm_output[0]) | (fsm_output[2]);
  assign VCOL_if_4_and_cse = run_wen & (~((~ (fsm_output[1])) | or_dcpl_28 | (~ VCOL_if_4_VCOL_if_4_and_itm_1)));
  assign and_cse = VCOL_else_2_else_aif_equal_tmp & VROW_equal_tmp;
  assign and_253_cse = operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 &
      VCOL_else_2_else_aif_equal_tmp;
  assign nand_37_cse = ~(reg_operator_11_false_6_nor_itm_1_cse & (VCOL_x_sva[0]));
  assign nand_39_cse = ~(exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 & VCOL_stage_0_1);
  assign VCOL_else_3_if_for_and_5_cse = operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign nand_nl = ~(operator_11_false_4_operator_11_false_4_nor_tmp & (~ mux_tmp_3));
  assign mux_9_nl = MUX_s_1_2_2(nand_nl, mux_59_cse, operator_11_false_1_nor_tmp);
  assign rdbuf1_pix_and_1_cse = run_wen & (((VCOL_x_sva[0]) & (~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1)
      & exitL_exitL_exit_VCOL_else_3_if_for_1_sva) | VCOL_else_3_if_for_and_5_cse)
      & VCOL_stage_0_2 & (fsm_output[1]) & (mux_9_nl | (~ VCOL_stage_0_1));
  assign nand_41_cse = ~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) & VCOL_stage_0_1);
  assign or_204_cse = (~ VCOL_stage_0_1) | VCOL_else_2_else_aif_equal_tmp;
  assign or_206_nl = (ctrl_signal_rsci_idat[0]) | (~ VCOL_stage_0_1) | VCOL_else_2_else_aif_equal_tmp;
  assign or_205_nl = (~ (ctrl_signal_rsci_idat[0])) | (~ VCOL_stage_0_1) | VCOL_else_2_else_aif_equal_tmp;
  assign mux_83_nl = MUX_s_1_2_2(or_206_nl, or_205_nl, ctrl_signal_rsci_idat[1]);
  assign nor_nl = ~((VROW_y_sva!=10'b0000000001) | (VCOL_x_sva_2!=11'b00000000001));
  assign mux_84_cse = MUX_s_1_2_2(mux_83_nl, or_204_cse, nor_nl);
  assign nor_78_cse = ~((VCOL_x_sva!=11'b00000000001));
  assign or_226_cse = (VCOL_x_sva[10:1]!=10'b0000000000);
  assign or_222_cse = (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1) | operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1;
  assign operator_10_false_1_and_cse = run_wen & VCOL_aelse_VCOL_aelse_and_cse;
  assign operator_11_false_6_and_cse = run_wen & (~ mux_tmp_3) & VCOL_stage_0_1;
  assign and_268_cse = (VCOL_x_sva[0]) & VROW_equal_tmp & reg_operator_11_false_6_nor_itm_1_cse;
  assign nor_24_nl = ~(VCOL_else_2_else_aif_equal_tmp | (~ or_tmp_20));
  assign mux_21_nl = MUX_s_1_2_2(or_tmp_22, nor_24_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign mux_23_nl = MUX_s_1_2_2(or_tmp_20, mux_21_nl, VCOL_stage_0_2);
  assign mux_24_nl = MUX_s_1_2_2(mux_23_nl, (~ and_dcpl_5), VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp);
  assign VCOL_and_41_cse = run_wen & mux_24_nl & VCOL_stage_0_1;
  assign or_251_cse = VCOL_and_15_cse_1 | VCOL_equal_tmp_1_1 | VCOL_equal_tmp_1;
  assign and_232_cse = or_251_cse & (fsm_output[1]) & VCOL_stage_0_2 & run_wen;
  assign mux_26_nl = MUX_s_1_2_2((~ (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0])),
      (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]), VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign or_41_nl = VCOL_else_2_else_aif_equal_tmp | mux_tmp_10;
  assign mux_27_nl = MUX_s_1_2_2(mux_26_nl, or_41_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign mux_30_nl = MUX_s_1_2_2(mux_tmp_10, mux_27_nl, VCOL_stage_0_2);
  assign VCOL_else_3_if_for_and_52_cse = run_wen & (~ mux_30_nl) & VCOL_stage_0_1;
  assign or_43_cse = VCOL_else_2_else_aif_equal_tmp | (ctrl_signal_rsci_idat[0]);
  assign pix_result_dy_and_cse = run_wen & (~((~ (fsm_output[1])) | or_dcpl_34));
  assign nor_25_nl = ~((~ lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3) | exitL_exitL_exit_VCOL_else_3_if_for_1_sva);
  assign nor_26_nl = ~(exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 | (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10));
  assign mux_34_nl = MUX_s_1_2_2(nor_25_nl, nor_26_nl, VCOL_stage_0_2);
  assign pix_result_dy_and_3_cse = run_wen & (~ or_dcpl_34) & mux_34_nl & VCOL_stage_0_1;
  assign or_53_cse = (~ lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3) | exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign mux_52_nl = MUX_s_1_2_2(or_53_cse, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1,
      VCOL_stage_0_2);
  assign VCOL_mux_6_cse = MUX_v_2_2_2(VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1,
      ctrl_signal_rsci_idat, mux_52_nl);
  assign and_179_cse = VCOL_stage_0_2 & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign or_88_nl = exitL_exitL_exit_VCOL_else_3_if_for_1_sva | (~ lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1_mx0w0);
  assign mux_54_nl = MUX_s_1_2_2(exitL_exitL_exit_VCOL_else_3_if_for_1_sva, or_88_nl,
      VCOL_stage_0_2);
  assign mux_55_nl = MUX_s_1_2_2(and_179_cse, mux_54_nl, VCOL_stage_0_1);
  assign and_125_rmff = mux_55_nl & (fsm_output[1]);
  assign nand_23_nl = ~(exitL_exitL_exit_VCOL_else_3_if_for_1_sva & (VCOL_x_sva[0]));
  assign or_91_nl = (~ VCOL_else_3_if_for_mux_46_tmp_0) | (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1)
      | VCOL_else_2_else_aif_equal_tmp;
  assign mux_58_nl = MUX_s_1_2_2(nand_23_nl, or_91_nl, VCOL_stage_0_2);
  assign mux_59_cse = MUX_s_1_2_2(mux_58_nl, mux_tmp_3, operator_11_false_4_operator_11_false_4_nor_tmp);
  assign and_51_nl = VCOL_stage_0_2 & nor_tmp_13;
  assign and_181_nl = (VCOL_x_sva[0]) & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign or_173_nl = (~((~ VCOL_else_3_if_for_mux_46_tmp_0) | (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1)
      | VCOL_else_2_else_aif_equal_tmp)) | nor_tmp_13;
  assign mux_61_nl = MUX_s_1_2_2(and_181_nl, or_173_nl, VCOL_stage_0_2);
  assign nand_1_nl = ~(lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1_mx0w0 & (~
      nor_tmp_13));
  assign mux_60_nl = MUX_s_1_2_2(exitL_exitL_exit_VCOL_else_3_if_for_1_sva, nand_1_nl,
      VCOL_stage_0_2);
  assign or_92_nl = (VROW_y_sva!=10'b0000000000) | operator_11_false_4_operator_11_false_4_nor_tmp;
  assign mux_62_nl = MUX_s_1_2_2(mux_61_nl, mux_60_nl, or_92_nl);
  assign mux_63_nl = MUX_s_1_2_2(and_51_nl, mux_62_nl, VCOL_stage_0_1);
  assign and_137_rmff = mux_63_nl & (fsm_output[1]);
  assign VCOL_and_38_cse = run_wen & (~(or_dcpl_28 | (~ (fsm_output[1]))));
  assign VCOL_x_and_cse = exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 & VCOL_stage_0_2;
  assign VCOL_x_sva_mx1 = MUX_v_11_2_2(VCOL_x_sva, VCOL_x_sva_2, VCOL_x_and_cse);
  assign lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1_mx0w0 = VCOL_else_2_else_aif_equal_tmp
      | (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign nl_operator_4_false_1_acc_nl = i_1_sva_1_mx0w0 + 4'b0111;
  assign operator_4_false_1_acc_nl = nl_operator_4_false_1_acc_nl[3:0];
  assign operator_4_false_1_acc_itm_3 = readslicef_4_1_3(operator_4_false_1_acc_nl);
  assign nl_operator_4_false_2_acc_nl = i_sva_2 + 4'b0111;
  assign operator_4_false_2_acc_nl = nl_operator_4_false_2_acc_nl[3:0];
  assign operator_4_false_2_acc_itm_3 = readslicef_4_1_3(operator_4_false_2_acc_nl);
  assign VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp = ~(operator_4_false_1_acc_itm_3
      | operator_4_false_2_acc_itm_3);
  assign exitL_exitL_exit_VCOL_else_3_if_for_1_sva_mx1 = MUX_s_1_2_2(exitL_exitL_exit_VCOL_else_3_if_for_1_sva,
      (~ lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1_mx0w0), VCOL_stage_0_2);
  assign VCOL_aelse_VCOL_aelse_and_cse = VCOL_stage_0_1 & nand_4_cse;
  assign VCOL_else_3_if_for_or_6_nl = (~(exitL_exitL_exit_VCOL_else_3_if_for_1_sva
      & (~((~ VCOL_land_lpi_3_dfm_1) & VCOL_else_3_if_for_and_29_cse_1)))) | ((~
      VCOL_land_lpi_3_dfm_1) & VCOL_else_2_else_else_or_6_m1c_1 & VCOL_else_3_if_for_and_30_m1c_1);
  assign VCOL_else_3_if_for_or_7_nl = (VCOL_land_lpi_3_dfm_1 & VCOL_else_2_else_else_or_6_m1c_1
      & VCOL_else_3_if_for_and_30_m1c_1) | (VCOL_land_lpi_3_dfm_1 & VCOL_else_3_if_for_and_29_cse_1);
  assign VCOL_else_3_if_for_or_8_nl = (VCOL_else_2_else_aif_equal_tmp & VCOL_else_2_else_else_and_3_m1c_1
      & VCOL_else_3_if_for_and_30_m1c_1) | (and_253_cse & (~ and_268_cse) & VCOL_else_3_if_for_and_8_m1c_1);
  assign VCOL_else_3_if_for_or_9_nl = (VROW_equal_tmp & VCOL_else_2_else_else_and_3_m1c_1
      & VCOL_else_3_if_for_and_30_m1c_1) | VCOL_else_3_if_for_and_31_cse_1;
  assign VCOL_else_3_if_for_and_45_nl = and_cse & VCOL_else_3_if_for_and_30_m1c_1;
  assign pix_2_lpi_3_dfm_9_mx1w0 = MUX1HOT_v_8_5_2(pix_2_lpi_3, dat_in_rsci_idat_mxwt,
      pix_5_lpi_3, pix_1_lpi_3_dfm_10, pix_4_lpi_3_dfm_mx0, {VCOL_else_3_if_for_or_6_nl
      , VCOL_else_3_if_for_or_7_nl , VCOL_else_3_if_for_or_8_nl , VCOL_else_3_if_for_or_9_nl
      , VCOL_else_3_if_for_and_45_nl});
  assign VCOL_else_3_if_for_nand_12_nl = ~(exitL_exitL_exit_VCOL_else_3_if_for_1_sva
      & (~(VCOL_lor_lpi_3_dfm_1 & (~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1)
      & VCOL_else_3_if_for_or_m1c_1)));
  assign VCOL_else_3_if_for_and_41_nl = (~((VCOL_x_sva[0]) | VCOL_lor_lpi_3_dfm_1
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1)) & VCOL_else_3_if_for_or_m1c_1;
  assign VCOL_and_8_nl = (VCOL_x_sva[0]) & (~ VCOL_lor_lpi_3_dfm_1) & (~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1)
      & VCOL_else_3_if_for_or_m1c_1;
  assign VCOL_else_3_if_for_and_42_nl = operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      & VCOL_else_3_if_for_or_m1c_1;
  assign VCOL_else_3_if_for_and_33_nl = ((VCOL_else_2_else_aif_equal_tmp & (~ operator_10_false_1_operator_10_false_1_and_cse_sva_1_1)
      & VCOL_else_2_else_else_else_and_tmp_1) | and_cse) & VCOL_and_m1c_1;
  assign VCOL_else_3_if_for_or_3_nl = (operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & VCOL_else_2_else_else_else_and_tmp_1 & VCOL_and_m1c_1) | VCOL_else_3_if_for_and_29_cse_1;
  assign VCOL_and_11_nl = and_253_cse & VCOL_VCOL_nor_1_m1c_1 & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign pix_0_lpi_3_dfm_9_mx1w0 = MUX1HOT_v_8_7_2(pix_0_lpi_3, (rdbuf1_pix_lpi_3[7:0]),
      (rdbuf1_pix_lpi_3[15:8]), (line_buf1_rsci_q_d[15:8]), pix_3_lpi_3_dfm_mx0,
      pix_1_lpi_3_dfm_10, pix_4_lpi_3_dfm_mx0, {VCOL_else_3_if_for_nand_12_nl , VCOL_else_3_if_for_and_41_nl
      , VCOL_and_8_nl , VCOL_else_3_if_for_and_42_nl , VCOL_else_3_if_for_and_33_nl
      , VCOL_else_3_if_for_or_3_nl , VCOL_and_11_nl});
  assign operator_10_false_1_nor_tmp = ~((VROW_y_sva[9:1]!=9'b000000000));
  assign operator_10_false_1_operator_10_false_1_and_cse_sva_1 = (VROW_y_sva[0])
      & operator_10_false_1_nor_tmp;
  assign operator_11_false_1_nor_tmp = ~((VCOL_x_sva_mx1[10:1]!=10'b0000000000));
  assign operator_11_false_4_operator_11_false_4_nor_tmp = ~((VCOL_x_sva_mx1!=11'b00000000000));
  assign VCOL_else_3_if_for_and_43_nl = (~ VCOL_or_8_tmp_1) & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign VCOL_else_3_if_for_and_44_nl = VCOL_or_8_tmp_1 & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign pix_1_lpi_3_dfm_9_mx1w0 = MUX1HOT_v_8_3_2(pix_1_lpi_3, pix_1_lpi_3_dfm_10,
      pix_4_lpi_3_dfm_mx0, {(~ exitL_exitL_exit_VCOL_else_3_if_for_1_sva) , VCOL_else_3_if_for_and_43_nl
      , VCOL_else_3_if_for_and_44_nl});
  assign VCOL_VCOL_oelse_operator_11_false_or_tmp = (VCOL_x_sva_mx1!=11'b00000000000);
  assign VCOL_equal_tmp_4 = ~((VCOL_mux_6_cse!=2'b00));
  assign VCOL_else_3_if_for_nor_6_nl = ~(MUX_v_4_2_2((z_out_1[3:0]), 4'b1111, VCOL_else_3_if_for_nor_ovfl_sva_1));
  assign VCOL_else_3_if_for_VCOL_else_3_if_for_nor_4_nl = ~(MUX_v_4_2_2(VCOL_else_3_if_for_nor_6_nl,
      4'b1111, VCOL_else_3_if_for_and_unfl_sva_1));
  assign pix_result_7_4_lpi_3_dfm_2_mx0w1 = MUX1HOT_v_4_4_2((pix_4_lpi_3_dfm_1_mx1[7:4]),
      VCOL_else_3_if_for_VCOL_else_3_if_for_nor_4_nl, pix_result_7_4_lpi_3, (VCOL_else_3_else_if_ac_fixed_cctor_2_15_1_sva_1[6:3]),
      {VCOL_equal_tmp_1 , VCOL_equal_tmp_1_1 , VCOL_or_2_cse_1 , VCOL_and_15_cse_1});
  assign VCOL_else_3_if_for_nor_3_nl = ~(MUX_v_8_2_2((z_out_1[11:4]), 8'b11111111,
      VCOL_else_3_if_for_nor_ovfl_sva_1));
  assign VCOL_else_3_if_for_VCOL_else_3_if_for_nor_1_nl = ~(MUX_v_8_2_2(VCOL_else_3_if_for_nor_3_nl,
      8'b11111111, VCOL_else_3_if_for_and_unfl_sva_1));
  assign VCOL_mux1h_11_nl = MUX1HOT_v_8_3_2(VCOL_else_3_if_for_VCOL_else_3_if_for_nor_1_nl,
      pix_result_15_8_lpi_3, (VCOL_else_3_else_if_ac_fixed_cctor_2_15_1_sva_1[14:7]),
      {VCOL_equal_tmp_1_1 , VCOL_or_2_cse_1 , VCOL_and_15_cse_1});
  assign VCOL_not_37_nl = ~ VCOL_equal_tmp_1;
  assign pix_result_15_8_lpi_3_dfm_2_mx0w1 = MUX_v_8_2_2(8'b00000000, VCOL_mux1h_11_nl,
      VCOL_not_37_nl);
  assign VCOL_else_3_if_for_mux_2_nl = MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3,
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1_mx0w0, VCOL_stage_0_2);
  assign lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_2 = VCOL_else_3_if_for_mux_2_nl
      & (~ exitL_exitL_exit_VCOL_else_3_if_for_1_sva_mx1);
  assign VCOL_mux1h_10_nl = MUX1HOT_s_1_3_2((z_out_1[13]), pix_result_16_lpi_3, (VCOL_else_3_else_if_acc_sat_sva_1[17]),
      {VCOL_equal_tmp_1_1 , VCOL_or_2_cse_1 , VCOL_and_15_cse_1});
  assign pix_result_16_lpi_3_dfm_2_mx1w0 = VCOL_mux1h_10_nl & (~ VCOL_equal_tmp_1);
  assign VCOL_VCOL_and_6_cse = MUX_v_4_2_2(4'b0000, i_1_lpi_3_dfm_1_1, lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_2);
  assign nl_i_1_sva_1_mx0w0 = VCOL_VCOL_and_6_cse + 4'b0001;
  assign i_1_sva_1_mx0w0 = nl_i_1_sva_1_mx0w0[3:0];
  assign nl_i_sva_2 = i_lpi_3_dfm_2 + 4'b0001;
  assign i_sva_2 = nl_i_sva_2[3:0];
  assign VCOL_equal_tmp_6 = (VCOL_mux_6_cse==2'b10);
  assign VCOL_equal_tmp_7 = (VCOL_mux_6_cse==2'b11);
  assign nor_45_nl = ~((~ exitL_exitL_exit_VCOL_else_3_if_for_1_sva) | (VCOL_x_sva[0]));
  assign nor_46_nl = ~(VCOL_else_3_if_for_mux_46_tmp_0 | (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1)
      | VCOL_else_2_else_aif_equal_tmp);
  assign mux_57_cse = MUX_s_1_2_2(nor_45_nl, nor_46_nl, VCOL_stage_0_2);
  assign VCOL_else_3_if_for_and_24_nl = (~ operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1)
      & exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign VCOL_else_3_if_for_and_28_nl = operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1
      & exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign VCOL_VCOL_slc_pix_39_32_2_lpi_3_dfm_mx1w0 = MUX1HOT_v_8_3_2(VCOL_VCOL_slc_pix_39_32_2_lpi_4,
      pix_1_lpi_3_dfm_9_mx1w0, pix_4_lpi_3_dfm_1_mx1, {(~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1)
      , VCOL_else_3_if_for_and_24_nl , VCOL_else_3_if_for_and_28_nl});
  assign VCOL_VCOL_and_8_nl = MUX_v_3_2_2(3'b000, pix_result_3_1_lpi_3, lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign VCOL_else_3_if_for_nor_2_nl = ~(MUX_v_3_2_2(VCOL_VCOL_and_8_nl, 3'b111,
      VCOL_else_3_if_for_nor_ovfl_sva_1));
  assign VCOL_else_3_if_for_VCOL_else_3_if_for_nor_nl = ~(MUX_v_3_2_2(VCOL_else_3_if_for_nor_2_nl,
      3'b111, VCOL_else_3_if_for_and_unfl_sva_1));
  assign pix_result_3_1_lpi_3_dfm_2_mx0w1 = MUX1HOT_v_3_4_2((pix_4_lpi_3_dfm_1_mx1[3:1]),
      VCOL_else_3_if_for_VCOL_else_3_if_for_nor_nl, pix_result_3_1_lpi_3, (VCOL_else_3_else_if_ac_fixed_cctor_2_15_1_sva_1[2:0]),
      {VCOL_equal_tmp_1 , VCOL_equal_tmp_1_1 , VCOL_or_2_cse_1 , VCOL_and_15_cse_1});
  assign VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1_mx0 = MUX_s_1_2_2(VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1,
      VCOL_VCOL_oelse_operator_11_false_or_tmp, mux_65_itm);
  assign VCOL_else_3_if_for_VCOL_else_3_if_for_nor_2_nl = ~((~((pix_result_0_lpi_3
      & lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1) | VCOL_else_3_if_for_nor_ovfl_sva_1))
      | VCOL_else_3_if_for_and_unfl_sva_1);
  assign VCOL_else_3_else_if_VCOL_else_3_else_if_nor_nl = ~((~((VCOL_else_3_else_if_acc_sat_sva_1[0])
      | VCOL_else_3_else_if_nor_ovfl_2_sva_1)) | VCOL_else_3_else_if_and_unfl_2_sva_1);
  assign pix_result_0_lpi_3_dfm_2_mx1w0 = MUX1HOT_s_1_4_2((pix_4_lpi_3_dfm_1_mx1[0]),
      VCOL_else_3_if_for_VCOL_else_3_if_for_nor_2_nl, pix_result_0_lpi_3, VCOL_else_3_else_if_VCOL_else_3_else_if_nor_nl,
      {VCOL_equal_tmp_1 , VCOL_equal_tmp_1_1 , VCOL_or_2_cse_1 , VCOL_and_15_cse_1});
  assign nl_operator_11_false_acc_nl = ({1'b1 , widthIn}) + conv_u2s_11_12(~ VCOL_x_sva_mx1);
  assign operator_11_false_acc_nl = nl_operator_11_false_acc_nl[11:0];
  assign operator_11_false_acc_itm_11_1 = readslicef_12_1_11(operator_11_false_acc_nl);
  assign nl_operator_10_false_acc_nl = ({1'b1 , heightIn}) + conv_u2s_10_11(~ VROW_y_sva);
  assign operator_10_false_acc_nl = nl_operator_10_false_acc_nl[10:0];
  assign operator_10_false_acc_itm_10_1 = readslicef_11_1_10(operator_10_false_acc_nl);
  assign i_lpi_3_dfm_2 = MUX_v_4_2_2(4'b0000, i_lpi_3_dfm_1_1, lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_2);
  assign pix_3_lpi_3_dfm_mx0 = MUX_v_8_2_2(pix_3_lpi_3, (line_buf1_rsci_q_d[7:0]),
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign pix_4_lpi_3_dfm_mx0 = MUX_v_8_2_2(pix_4_lpi_3, (line_buf0_rsci_q_d[7:0]),
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign VCOL_VCOL_nor_7_nl = ~((VCOL_x_sva[0]) | reg_operator_11_false_6_nor_itm_1_cse
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign VCOL_and_31_nl = reg_operator_11_false_6_nor_itm_1_cse & (~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign pix_1_lpi_3_dfm_10 = MUX1HOT_v_8_4_2((rdbuf0_pix_lpi_3[7:0]), (rdbuf0_pix_lpi_3[15:8]),
      pix_1_lpi_3, (line_buf0_rsci_q_d[15:8]), {VCOL_VCOL_nor_7_nl , VCOL_and_10_itm_1
      , VCOL_and_31_nl , operator_11_false_4_operator_11_false_4_nor_cse_sva_1});
  assign nor_40_nl = ~(reg_operator_11_false_6_nor_itm_1_cse | (~ VCOL_else_2_else_else_else_nor_1_tmp)
      | (~ (VCOL_x_sva[0])) | VCOL_else_2_else_aif_equal_tmp);
  assign or_171_nl = (VCOL_else_2_else_else_else_nor_1_tmp & (VCOL_x_sva[0])) | VCOL_else_2_else_aif_equal_tmp;
  assign nor_41_nl = ~((VCOL_x_sva[0]) | (~ VCOL_else_2_else_aif_equal_tmp));
  assign mux_66_nl = MUX_s_1_2_2(or_171_nl, nor_41_nl, reg_operator_11_false_6_nor_itm_1_cse);
  assign mux_67_nl = MUX_s_1_2_2(nor_40_nl, mux_66_nl, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign or_107_nl = mux_67_nl | (~(exitL_exitL_exit_VCOL_else_3_if_for_1_sva & VROW_equal_tmp))
      | VCOL_land_1_lpi_3_dfm_1;
  assign pix_5_lpi_3_dfm_6_mx1 = MUX_v_8_2_2(pix_4_lpi_3_dfm_mx0, pix_5_lpi_3, or_107_nl);
  assign VCOL_else_2_else_else_else_nor_1_tmp = ~((VCOL_x_sva[10:1]!=10'b0000000000));
  assign VCOL_else_2_else_else_else_unequal_tmp_1 = ~((VCOL_x_sva[0]) & VCOL_else_2_else_else_else_nor_1_tmp);
  assign VCOL_else_2_else_aif_equal_tmp = VCOL_x_sva == widthIn;
  assign VCOL_else_2_else_else_or_6_m1c_1 = VCOL_else_2_else_else_VCOL_else_2_else_else_nor_3_cse_1
      | (((~(VCOL_else_2_else_aif_equal_tmp | operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      | VROW_equal_tmp)) | VCOL_else_2_else_else_else_else_and_5_tmp_1) & VCOL_else_2_else_else_and_3_m1c_1);
  assign VCOL_else_2_else_else_and_3_m1c_1 = VCOL_else_2_else_else_else_unequal_tmp_1
      & (~ and_cse);
  assign VCOL_else_2_else_else_else_and_tmp_1 = (~ VROW_equal_tmp) & VCOL_else_2_else_else_else_unequal_tmp_1;
  assign VROW_equal_tmp = VROW_y_sva == heightIn;
  assign VCOL_else_2_else_else_and_7_m1c_1 = VCOL_else_2_else_else_else_unequal_tmp_1
      & (~ and_cse) & VCOL_else_2_VCOL_else_2_nor_1_m1c_1;
  assign VCOL_else_2_VCOL_else_2_nor_1_m1c_1 = ~(and_253_cse | and_268_cse);
  assign VCOL_else_2_else_else_else_else_and_5_tmp_1 = operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & (~ VROW_equal_tmp);
  assign VCOL_VCOL_nor_5_m1c_1 = ~(and_253_cse | VCOL_or_tmp_1);
  assign VCOL_or_tmp_1 = and_268_cse | VCOL_land_1_lpi_3_dfm_1;
  assign VCOL_VCOL_nor_1_m1c_1 = ~(and_268_cse | VCOL_land_1_lpi_3_dfm_1);
  assign VCOL_lor_lpi_3_dfm_1 = ~(nand_37_cse & VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1);
  assign VCOL_else_3_if_for_nor_ovfl_sva_1 = ~((z_out_1[13:12]!=2'b01));
  assign VCOL_else_3_if_for_and_unfl_sva_1 = (z_out_1[13:12]==2'b10);
  assign nl_operator_17_17_true_AC_RND_AC_SAT_acc_nl = ({1'b1 , (~ pix_result_15_8_lpi_3_dfm_2_mx0w1)})
      + 9'b000000001;
  assign operator_17_17_true_AC_RND_AC_SAT_acc_nl = nl_operator_17_17_true_AC_RND_AC_SAT_acc_nl[8:0];
  assign operator_17_17_true_AC_RND_AC_SAT_acc_itm_8_1 = readslicef_9_1_8(operator_17_17_true_AC_RND_AC_SAT_acc_nl);
  assign VCOL_or_2_cse_1 = ((~ lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3) & VCOL_equal_tmp_2_1)
      | VCOL_equal_tmp_3_1;
  assign VCOL_else_3_else_if_nor_6_nl = ~(MUX_v_15_2_2((VCOL_else_3_else_if_acc_sat_sva_1[15:1]),
      15'b111111111111111, VCOL_else_3_else_if_nor_ovfl_2_sva_1));
  assign VCOL_else_3_else_if_ac_fixed_cctor_2_15_1_sva_1 = ~(MUX_v_15_2_2(VCOL_else_3_else_if_nor_6_nl,
      15'b111111111111111, VCOL_else_3_else_if_and_unfl_2_sva_1));
  assign VCOL_and_15_cse_1 = lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3 & VCOL_equal_tmp_2_1;
  assign VCOL_else_3_if_for_nand_14_nl = ~(exitL_exitL_exit_VCOL_else_3_if_for_1_sva
      & (~((~ operator_11_false_4_operator_11_false_4_nor_cse_sva_1) & VCOL_else_3_if_for_and_46_m1c_1)));
  assign VCOL_else_3_if_for_and_50_nl = operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      & VCOL_else_3_if_for_and_46_m1c_1;
  assign VCOL_else_3_if_for_and_47_nl = VCOL_or_10_tmp_1 & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign pix_3_lpi_3_dfm_11 = MUX1HOT_v_8_3_2(pix_3_lpi_3, (line_buf1_rsci_q_d[7:0]),
      pix_4_lpi_3_dfm_mx0, {VCOL_else_3_if_for_nand_14_nl , VCOL_else_3_if_for_and_50_nl
      , VCOL_else_3_if_for_and_47_nl});
  assign nand_22_nl = ~(exitL_exitL_exit_VCOL_else_3_if_for_1_sva & operator_11_false_4_operator_11_false_4_nor_cse_sva_1);
  assign pix_4_lpi_3_dfm_1_mx1 = MUX_v_8_2_2((line_buf0_rsci_q_d[7:0]), pix_4_lpi_3,
      nand_22_nl);
  assign VCOL_else_3_if_for_nand_8_nl = ~(exitL_exitL_exit_VCOL_else_3_if_for_1_sva
      & (~((((~ VCOL_else_2_else_else_else_else_and_5_tmp_1) & VCOL_else_2_else_else_and_7_m1c_1)
      | (and_cse & VCOL_else_2_VCOL_else_2_nor_1_m1c_1)) & VCOL_else_3_if_for_and_8_m1c_1)));
  assign VCOL_else_3_if_for_and_36_nl = ((VCOL_else_2_else_else_VCOL_else_2_else_else_nor_3_cse_1
      & VCOL_else_2_VCOL_else_2_nor_1_m1c_1) | and_268_cse) & VCOL_else_3_if_for_and_8_m1c_1;
  assign VCOL_else_3_if_for_and_38_nl = ((VCOL_else_2_else_else_else_else_and_5_tmp_1
      & VCOL_else_2_else_else_and_7_m1c_1) | VCOL_else_2_and_3_cse_1) & VCOL_else_3_if_for_and_8_m1c_1;
  assign pix_6_lpi_3_dfm_9 = MUX1HOT_v_8_4_2(pix_6_lpi_3, pix_3_lpi_3_dfm_mx0, pix_7_lpi_3,
      pix_4_lpi_3_dfm_mx0, {VCOL_else_3_if_for_nand_8_nl , VCOL_else_3_if_for_and_36_nl
      , VCOL_else_3_if_for_and_38_nl , VCOL_else_3_if_for_and_29_cse_1});
  assign VCOL_else_3_if_for_nand_6_nl = ~(exitL_exitL_exit_VCOL_else_3_if_for_1_sva
      & (~((((~ VROW_equal_tmp) & VCOL_else_2_else_else_and_3_m1c_1 & VCOL_else_2_VCOL_else_2_nor_1_m1c_1)
      | VCOL_else_2_and_3_cse_1) & VCOL_else_3_if_for_and_8_m1c_1)));
  assign VCOL_else_3_if_for_or_4_nl = (VCOL_else_2_else_else_VCOL_else_2_else_else_nor_3_cse_1
      & VCOL_else_2_VCOL_else_2_nor_1_m1c_1 & VCOL_else_3_if_for_and_8_m1c_1) | VCOL_else_3_if_for_and_29_cse_1;
  assign VCOL_else_2_and_13_nl = ((VROW_equal_tmp & VCOL_else_2_else_else_and_3_m1c_1)
      | and_cse) & VCOL_else_2_VCOL_else_2_nor_1_m1c_1 & VCOL_else_3_if_for_and_8_m1c_1;
  assign pix_8_lpi_3_dfm_8 = MUX1HOT_v_8_4_2(pix_8_lpi_3, pix_5_lpi_3, pix_7_lpi_3,
      pix_4_lpi_3_dfm_mx0, {VCOL_else_3_if_for_nand_6_nl , VCOL_else_3_if_for_or_4_nl
      , VCOL_else_2_and_13_nl , VCOL_else_3_if_for_and_31_cse_1});
  assign nl_VCOL_else_3_else_if_acc_sat_sva_1 = conv_s2s_17_18({(z_out_1[17]) , pix_result_dx_15_1_sva_2
      , pix_result_dx_0_sva_2}) + conv_s2s_17_18({(VCOL_else_3_else_if_for_1_acc_psp_1_sva_1[17])
      , pix_result_dy_15_1_sva_2 , pix_result_dy_0_sva_2});
  assign VCOL_else_3_else_if_acc_sat_sva_1 = nl_VCOL_else_3_else_if_acc_sat_sva_1[17:0];
  assign VCOL_else_3_else_if_nor_ovfl_2_sva_1 = ~((VCOL_else_3_else_if_acc_sat_sva_1[17:16]!=2'b01));
  assign VCOL_else_3_else_if_and_unfl_2_sva_1 = (VCOL_else_3_else_if_acc_sat_sva_1[17:16]==2'b10);
  assign pix_result_dx_conc_itm_15_1 = MUX_v_15_2_2(15'b000000000000000, pix_result_dx_15_1_lpi_3,
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign VCOL_else_3_else_if_for_nor_2_nl = ~(MUX_v_15_2_2((z_out_1[15:1]), 15'b111111111111111,
      VCOL_else_3_else_if_for_nor_ovfl_sva_1));
  assign pix_result_dx_15_1_sva_2 = ~(MUX_v_15_2_2(VCOL_else_3_else_if_for_nor_2_nl,
      15'b111111111111111, VCOL_else_3_else_if_for_and_unfl_sva_1));
  assign pix_result_dx_0_sva_2 = ~((~((z_out_1[0]) | VCOL_else_3_else_if_for_nor_ovfl_sva_1))
      | VCOL_else_3_else_if_for_and_unfl_sva_1);
  assign VCOL_VCOL_and_13_nl = pix_result_dy_16_lpi_3 & lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign VCOL_VCOL_and_14_nl = MUX_v_15_2_2(15'b000000000000000, pix_result_dy_15_1_lpi_3,
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign VCOL_VCOL_and_15_nl = pix_result_dy_0_lpi_3 & lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign nl_operator_10_10_true_AC_TRN_AC_SAT_2_mul_nl = $signed(conv_u2s_8_9(VCOL_else_3_if_for_mux_61))
      * $signed(VCOL_else_3_else_if_for_1_mux_itm_1);
  assign operator_10_10_true_AC_TRN_AC_SAT_2_mul_nl = nl_operator_10_10_true_AC_TRN_AC_SAT_2_mul_nl[9:0];
  assign nl_VCOL_else_3_else_if_for_1_acc_psp_1_sva_1 = conv_s2s_17_18({VCOL_VCOL_and_13_nl
      , VCOL_VCOL_and_14_nl , VCOL_VCOL_and_15_nl}) + conv_s2s_10_18(operator_10_10_true_AC_TRN_AC_SAT_2_mul_nl);
  assign VCOL_else_3_else_if_for_1_acc_psp_1_sva_1 = nl_VCOL_else_3_else_if_for_1_acc_psp_1_sva_1[17:0];
  assign VCOL_else_3_else_if_for_1_nor_2_nl = ~(MUX_v_15_2_2((VCOL_else_3_else_if_for_1_acc_psp_1_sva_1[15:1]),
      15'b111111111111111, VCOL_else_3_else_if_for_1_nor_ovfl_sva_1));
  assign pix_result_dy_15_1_sva_2 = ~(MUX_v_15_2_2(VCOL_else_3_else_if_for_1_nor_2_nl,
      15'b111111111111111, VCOL_else_3_else_if_for_1_and_unfl_sva_1));
  assign pix_result_dy_0_sva_2 = ~((~((VCOL_else_3_else_if_for_1_acc_psp_1_sva_1[0])
      | VCOL_else_3_else_if_for_1_nor_ovfl_sva_1)) | VCOL_else_3_else_if_for_1_and_unfl_sva_1);
  assign VCOL_else_3_else_if_for_1_nor_ovfl_sva_1 = ~((VCOL_else_3_else_if_for_1_acc_psp_1_sva_1[17:16]!=2'b01));
  assign VCOL_else_3_else_if_for_1_and_unfl_sva_1 = (VCOL_else_3_else_if_for_1_acc_psp_1_sva_1[17:16]==2'b10);
  assign VCOL_else_3_if_for_mux_13_nl = MUX_v_8_2_2(pix_4_lpi_3_dfm_mx0, pix_7_lpi_3,
      or_dcpl_40);
  assign VCOL_else_3_if_for_mux_61 = MUX_v_8_9_2(pix_0_lpi_3_dfm_9_mx1w0, pix_1_lpi_3_dfm_9_mx1w0,
      pix_2_lpi_3_dfm_9_mx1w0, pix_3_lpi_3_dfm_11, pix_4_lpi_3_dfm_1_mx1, pix_5_lpi_3_dfm_6_mx1,
      pix_6_lpi_3_dfm_9, VCOL_else_3_if_for_mux_13_nl, pix_8_lpi_3_dfm_8, i_1_lpi_3_dfm_1);
  assign VCOL_else_3_else_if_for_nor_ovfl_sva_1 = ~((z_out_1[17:16]!=2'b01));
  assign VCOL_else_3_else_if_for_and_unfl_sva_1 = (z_out_1[17:16]==2'b10);
  assign nl_VCOL_x_sva_2 = VCOL_x_sva + 11'b00000000001;
  assign VCOL_x_sva_2 = nl_VCOL_x_sva_2[10:0];
  assign VCOL_else_2_and_3_cse_1 = and_253_cse & (~ and_268_cse);
  assign VCOL_else_3_if_for_and_8_m1c_1 = (~ VCOL_land_1_lpi_3_dfm_1) & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign VCOL_else_2_else_else_VCOL_else_2_else_else_nor_3_cse_1 = ~(VCOL_else_2_else_else_else_unequal_tmp_1
      | and_cse);
  assign VCOL_else_3_if_for_and_29_cse_1 = VCOL_land_1_lpi_3_dfm_1 & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign VCOL_else_3_if_for_and_31_cse_1 = and_268_cse & VCOL_else_3_if_for_and_8_m1c_1;
  assign VCOL_else_3_if_for_and_46_m1c_1 = (~ VCOL_or_10_tmp_1) & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign VCOL_or_10_tmp_1 = (operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & (~ VROW_equal_tmp) & VCOL_else_2_else_else_else_unequal_tmp_1 & (~(and_cse
      | and_253_cse)) & VCOL_VCOL_nor_1_m1c_1) | (and_253_cse & VCOL_VCOL_nor_1_m1c_1)
      | VCOL_land_1_lpi_3_dfm_1;
  assign VCOL_else_3_if_for_and_30_m1c_1 = VCOL_else_2_VCOL_else_2_nor_1_m1c_1 &
      VCOL_else_3_if_for_and_8_m1c_1;
  assign VCOL_or_8_tmp_1 = (VCOL_else_2_else_aif_equal_tmp & VCOL_else_2_else_else_else_unequal_tmp_1
      & (~ and_cse) & VCOL_VCOL_nor_5_m1c_1) | (and_cse & VCOL_VCOL_nor_5_m1c_1)
      | (and_253_cse & (~ VCOL_or_tmp_1));
  assign VCOL_else_3_if_for_or_m1c_1 = (((~(VCOL_else_2_else_else_else_and_tmp_1
      | and_cse)) | ((~(VCOL_else_2_else_aif_equal_tmp | operator_10_false_1_operator_10_false_1_and_cse_sva_1_1))
      & VCOL_else_2_else_else_else_and_tmp_1)) & VCOL_and_m1c_1) | (and_268_cse &
      (~ VCOL_land_1_lpi_3_dfm_1) & exitL_exitL_exit_VCOL_else_3_if_for_1_sva);
  assign VCOL_and_m1c_1 = (~ and_253_cse) & VCOL_VCOL_nor_1_m1c_1 & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign VCOL_else_3_if_for_and_26_nl = (~ VCOL_else_2_else_aif_equal_tmp) & exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign VCOL_else_3_if_for_mux_46_tmp_0 = MUX_s_1_2_2((VCOL_x_sva[0]), (VCOL_x_sva_2[0]),
      VCOL_else_3_if_for_and_26_nl);
  assign nand_4_cse = ~(VCOL_else_2_else_aif_equal_tmp & exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1
      & VCOL_stage_0_2);
  assign and_dcpl_1 = VCOL_stage_0_1 & (~ operator_11_false_4_operator_11_false_4_nor_tmp);
  assign nor_16_cse = ~((VROW_y_sva!=10'b0000000000));
  assign and_dcpl_4 = VCOL_else_2_else_aif_equal_tmp & exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign and_dcpl_5 = and_dcpl_4 & VCOL_stage_0_2;
  assign or_dcpl_3 = and_dcpl_5 | (~ VCOL_stage_0_1);
  assign mux_tmp_3 = MUX_s_1_2_2((~ exitL_exitL_exit_VCOL_else_3_if_for_1_sva), lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1_mx0w0,
      VCOL_stage_0_2);
  assign mux_tmp_10 = MUX_s_1_2_2((~ (ctrl_signal_rsci_idat[0])), (ctrl_signal_rsci_idat[0]),
      ctrl_signal_rsci_idat[1]);
  assign or_tmp_20 = (ctrl_signal_rsci_idat!=2'b10);
  assign or_tmp_22 = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1!=2'b10);
  assign or_48_nl = VCOL_else_2_else_aif_equal_tmp | (ctrl_signal_rsci_idat!=2'b10);
  assign mux_35_nl = MUX_s_1_2_2(or_tmp_22, or_48_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign mux_36_itm = MUX_s_1_2_2(or_tmp_20, mux_35_nl, VCOL_stage_0_2);
  assign nand_7_nl = ~((ctrl_signal_rsci_idat[0]) & operator_4_false_1_acc_itm_3);
  assign or_49_nl = (ctrl_signal_rsci_idat[0]) | VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp;
  assign mux_tmp_37 = MUX_s_1_2_2(nand_7_nl, or_49_nl, ctrl_signal_rsci_idat[1]);
  assign or_dcpl_28 = ~(exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 & VCOL_stage_0_2);
  assign and_dcpl_23 = (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1) & VCOL_stage_0_2;
  assign and_dcpl_25 = or_222_cse & VCOL_stage_0_2;
  assign or_dcpl_34 = ~(VCOL_stage_0_2 & VCOL_equal_tmp_2_1);
  assign nor_tmp_13 = (operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1
      | (VCOL_else_1_else_asn_itm_1!=10'b0000000000)) & exitL_exitL_exit_VCOL_else_3_if_for_1_sva;
  assign mux_65_itm = MUX_s_1_2_2(exitL_exitL_exit_VCOL_else_3_if_for_1_sva, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1,
      VCOL_stage_0_2);
  assign or_tmp_69 = (~ VCOL_else_2_else_else_else_nor_1_tmp) | VCOL_else_2_else_aif_equal_tmp;
  assign mux_68_nl = MUX_s_1_2_2((~ VCOL_else_2_else_else_else_nor_1_tmp), or_tmp_69,
      operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign nor_42_nl = ~(reg_operator_11_false_6_nor_itm_1_cse | (~ or_tmp_69));
  assign mux_69_nl = MUX_s_1_2_2(mux_68_nl, nor_42_nl, VROW_equal_tmp);
  assign or_dcpl_40 = ~(((~(mux_69_nl | (~ (VCOL_x_sva[0])))) | VCOL_land_1_lpi_3_dfm_1)
      & exitL_exitL_exit_VCOL_else_3_if_for_1_sva);
  assign lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_mx0c1 = nand_4_cse & VCOL_stage_0_1
      & (fsm_output[1]);
  assign VCOL_if_1_not_nl = ~ operator_11_false_4_operator_11_false_4_nor_tmp;
  assign line_buf0_rsci_adr_d = MUX_v_10_2_2(10'b0000000000, z_out, VCOL_if_1_not_nl);
  assign VCOL_else_3_if_for_mux_6_nl = MUX_v_8_2_2(VCOL_VCOL_slc_pix_47_40_2_lpi_4,
      pix_2_lpi_3_dfm_9_mx1w0, VCOL_stage_0_2);
  assign VCOL_else_3_if_for_mux_5_nl = MUX_v_8_2_2(VCOL_VCOL_slc_pix_71_64_lpi_4,
      pix_5_lpi_3_dfm_6_mx1, VCOL_stage_0_2);
  assign line_buf0_rsci_d_d = {VCOL_else_3_if_for_mux_6_nl , VCOL_else_3_if_for_mux_5_nl};
  assign line_buf0_rsci_we_d_pff = mux_57_cse & and_dcpl_1 & (fsm_output[1]);
  assign line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_pff = (~ mux_59_cse)
      & VCOL_stage_0_1 & (fsm_output[1]);
  assign VCOL_if_1_nor_nl = ~((fsm_output[3]) | (fsm_output[0]) | (operator_11_false_4_operator_11_false_4_nor_tmp
      & (fsm_output[1])));
  assign line_buf1_rsci_adr_d = MUX_v_10_2_2(10'b0000000000, z_out, VCOL_if_1_nor_nl);
  assign VCOL_mux_12_nl = MUX_v_8_2_2(VCOL_VCOL_slc_pix_39_32_2_lpi_4, VCOL_VCOL_slc_pix_39_32_2_lpi_3_dfm_mx1w0,
      VCOL_stage_0_2);
  assign VCOL_else_3_if_for_mux_7_nl = MUX_v_8_2_2(VCOL_VCOL_slc_pix_63_56_lpi_4,
      pix_4_lpi_3_dfm_1_mx1, VCOL_stage_0_2);
  assign line_buf1_rsci_d_d = {VCOL_mux_12_nl , VCOL_else_3_if_for_mux_7_nl};
  assign nor_48_nl = ~((~ exitL_exitL_exit_VCOL_else_3_if_for_1_sva) | (VCOL_x_sva[0])
      | nor_16_cse);
  assign nor_49_nl = ~(VCOL_else_3_if_for_mux_46_tmp_0 | (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1)
      | VCOL_else_2_else_aif_equal_tmp | nor_16_cse);
  assign mux_64_nl = MUX_s_1_2_2(nor_48_nl, nor_49_nl, VCOL_stage_0_2);
  assign line_buf1_rsci_we_d_pff = mux_64_nl & and_dcpl_1 & (fsm_output[1]);
  assign or_183_nl = (~ VCOL_stage_0_2) | (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1)
      | VCOL_else_2_else_aif_equal_tmp;
  assign mux_tmp = MUX_s_1_2_2((VCOL_x_sva_2[0]), (VCOL_x_sva[0]), or_183_nl);
  assign or_tmp_129 = (~ mux_tmp) & (fsm_output[1]);
  assign or_tmp_131 = VCOL_equal_tmp_2_1 & (fsm_output[1]);
  assign exs_tmp_1_12 = pix_result_16_lpi_3 & lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign exs_tmp_1_3_0 = MUX_v_4_2_2(4'b0000, pix_result_7_4_lpi_3, lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign or_tmp_144 = (~(reg_operator_11_false_6_nor_itm_1_cse | (~ VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1)))
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_land_1_lpi_3_dfm_1;
  assign nor_85_nl = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 |
      (VCOL_x_sva[10:1]!=10'b0000000000) | or_tmp_144);
  assign nor_86_nl = ~((~ reg_operator_11_false_6_nor_itm_1_cse) | operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      | VCOL_land_1_lpi_3_dfm_1);
  assign mux_77_nl = MUX_s_1_2_2(nor_85_nl, nor_86_nl, VROW_equal_tmp);
  assign nand_tmp_4 = ~((VCOL_x_sva[0]) & mux_77_nl);
  assign nor_57_cse = ~(VROW_equal_tmp | (~ operator_10_false_1_operator_10_false_1_and_cse_sva_1_1));
  assign or_202_nl = nor_57_cse | VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_land_1_lpi_3_dfm_1;
  assign or_201_nl = (VCOL_x_sva[10:1]!=10'b0000000000) | or_tmp_144;
  assign mux_78_nl = MUX_s_1_2_2(or_tmp_144, or_201_nl, nor_57_cse);
  assign mux_tmp_79 = MUX_s_1_2_2(or_202_nl, mux_78_nl, VCOL_x_sva[0]);
  assign and_270_nl = ((~ VCOL_else_2_else_aif_equal_tmp) | (~ VROW_equal_tmp) |
      reg_operator_11_false_6_nor_itm_1_cse) & (VCOL_x_sva[0]);
  assign or_208_nl = VCOL_else_2_else_aif_equal_tmp | (~ VROW_equal_tmp) | (VCOL_x_sva[0]);
  assign mux_86_nl = MUX_s_1_2_2(and_270_nl, or_208_nl, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign nand_29_nl = ~((~(VCOL_else_2_else_aif_equal_tmp | (~ VROW_equal_tmp)))
      & nand_37_cse);
  assign mux_85_nl = MUX_s_1_2_2(and_268_cse, nand_29_nl, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign mux_87_nl = MUX_s_1_2_2(mux_86_nl, mux_85_nl, or_226_cse);
  assign or_tmp_156 = VCOL_land_1_lpi_3_dfm_1 | mux_87_nl;
  assign or_218_nl = VROW_equal_tmp | nor_78_cse;
  assign mux_93_nl = MUX_s_1_2_2(or_218_nl, and_268_cse, and_253_cse);
  assign or_tmp_165 = VCOL_land_1_lpi_3_dfm_1 | mux_93_nl;
  assign or_tmp_169 = operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_land_1_lpi_3_dfm_1;
  assign or_233_nl = (VCOL_x_sva_2[10:1]!=10'b0000000000) | (~ VCOL_stage_0_1);
  assign or_231_nl = (VROW_y_sva!=10'b0000000001) | (VCOL_x_sva_2[10:1]!=10'b0000000000)
      | (~ VCOL_stage_0_1);
  assign mux_tmp_99 = MUX_s_1_2_2(or_233_nl, or_231_nl, VCOL_x_sva_2[0]);
  assign nand_tmp_11 = ~(operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1
      & (~ VCOL_else_3_if_for_and_5_cse));
  assign or_241_nl = operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | (~ exitL_exitL_exit_VCOL_else_3_if_for_1_sva);
  assign mux_tmp_104 = MUX_s_1_2_2(or_241_nl, VCOL_else_3_if_for_and_5_cse, operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1);
  assign or_tmp_191 = (~((VCOL_x_sva[0]) | reg_operator_11_false_6_nor_itm_1_cse))
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_and_10_itm_1;
  assign or_tmp_195 = ~(nand_39_cse & or_tmp_191);
  assign and_dcpl_74 = VCOL_stage_0_1 & run_wen;
  assign nand_48_nl = ~((ctrl_signal_rsci_idat[1]) & (operator_4_false_1_acc_itm_3
      | operator_4_false_2_acc_itm_3));
  assign or_260_nl = (ctrl_signal_rsci_idat[1]) | (~ operator_4_false_1_acc_itm_3);
  assign mux_tmp_120 = MUX_s_1_2_2(nand_48_nl, or_260_nl, ctrl_signal_rsci_idat[0]);
  assign not_tmp_125 = ~(VCOL_stage_0_1 | (~ or_251_cse));
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_x_sva <= 11'b00000000000;
    end
    else if ( rst ) begin
      VCOL_x_sva <= 11'b00000000000;
    end
    else if ( (VCOL_x_and_cse | (fsm_output[2]) | (fsm_output[0])) & run_wen ) begin
      VCOL_x_sva <= MUX_v_11_2_2(11'b00000000000, VCOL_x_sva_mx1, not_233_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VROW_y_sva <= 10'b0000000000;
    end
    else if ( rst ) begin
      VROW_y_sva <= 10'b0000000000;
    end
    else if ( run_wen & VROW_y_or_cse ) begin
      VROW_y_sva <= MUX_v_10_2_2(10'b0000000000, z_out, VROW_y_not_2_nl);
    end
  end
  always @(posedge clk) begin
    if ( VCOL_if_4_and_cse ) begin
      dat_out_rsci_idat_7_4 <= ~(MUX_v_4_2_2(VCOL_if_4_nor_1_nl, 4'b1111, pix_result_16_lpi_3_dfm_2_mx1w0));
      dat_out_rsci_idat_0 <= ~((~(pix_result_0_lpi_3_dfm_2_mx1w0 | operator_17_17_true_AC_RND_AC_SAT_acc_itm_8_1))
          | pix_result_16_lpi_3_dfm_2_mx1w0);
      dat_out_rsci_idat_3_1 <= ~(MUX_v_3_2_2(VCOL_if_4_nor_2_nl, 3'b111, pix_result_16_lpi_3_dfm_2_mx1w0));
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3 <= 1'b0;
    end
    else if ( rst ) begin
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3 <= 1'b0;
    end
    else if ( run_wen & (((and_dcpl_4 | (~ VCOL_stage_0_1)) & VCOL_stage_0_2 & (fsm_output[1]))
        | lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_mx0c1) ) begin
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3 <= MUX_s_1_2_2(lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1_mx0w0,
          VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp, lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_mx0c1);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      exitL_exitL_exit_VCOL_else_3_if_for_1_sva <= 1'b0;
      VCOL_stage_0_1 <= 1'b0;
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1 <= 1'b0;
      VCOL_stage_0_2 <= 1'b0;
      reg_dat_in_rsci_oswt_cse <= 1'b0;
      reg_dat_out_rsci_oswt_cse <= 1'b0;
      reg_line_buf0_rsci_cgo_cse <= 1'b0;
      reg_line_buf1_rsci_cgo_cse <= 1'b0;
      ctrl_signal_triosy_obj_iswt0 <= 1'b0;
    end
    else if ( rst ) begin
      exitL_exitL_exit_VCOL_else_3_if_for_1_sva <= 1'b0;
      VCOL_stage_0_1 <= 1'b0;
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1 <= 1'b0;
      VCOL_stage_0_2 <= 1'b0;
      reg_dat_in_rsci_oswt_cse <= 1'b0;
      reg_dat_out_rsci_oswt_cse <= 1'b0;
      reg_line_buf0_rsci_cgo_cse <= 1'b0;
      reg_line_buf1_rsci_cgo_cse <= 1'b0;
      ctrl_signal_triosy_obj_iswt0 <= 1'b0;
    end
    else if ( run_wen ) begin
      exitL_exitL_exit_VCOL_else_3_if_for_1_sva <= exitL_exitL_exit_VCOL_else_3_if_for_1_sva_mx1
          | VROW_y_or_cse;
      VCOL_stage_0_1 <= VCOL_aelse_VCOL_aelse_and_cse | VROW_y_or_cse;
      operator_11_false_4_operator_11_false_4_nor_cse_sva_1 <= operator_11_false_4_operator_11_false_4_nor_tmp;
      VCOL_stage_0_2 <= VCOL_aelse_VCOL_aelse_and_cse & (~ VROW_y_or_cse);
      reg_dat_in_rsci_oswt_cse <= (~ mux_tmp_3) & VCOL_stage_0_1 & (~ operator_10_false_acc_itm_10_1)
          & (~ operator_11_false_acc_itm_11_1) & (fsm_output[1]);
      reg_dat_out_rsci_oswt_cse <= VCOL_x_and_cse & VCOL_if_4_VCOL_if_4_and_itm_1
          & (fsm_output[1]);
      reg_line_buf0_rsci_cgo_cse <= and_125_rmff;
      reg_line_buf1_rsci_cgo_cse <= and_137_rmff;
      ctrl_signal_triosy_obj_iswt0 <= VROW_equal_tmp & (fsm_output[2]);
    end
  end
  always @(posedge clk) begin
    if ( ((mux_72_nl & (~ VCOL_land_1_lpi_3_dfm_1)) | VCOL_land_lpi_3_dfm_1) & exitL_exitL_exit_VCOL_else_3_if_for_1_sva
        & (fsm_output[1]) & VCOL_stage_0_2 & run_wen ) begin
      pix_2_lpi_3 <= pix_2_lpi_3_dfm_9_mx1w0;
    end
  end
  always @(posedge clk) begin
    if ( mux_76_nl & VCOL_stage_0_2 & (fsm_output[1]) & run_wen ) begin
      pix_5_lpi_3 <= MUX_v_8_2_2(pix_2_lpi_3_dfm_9_mx1w0, pix_5_lpi_3_dfm_6_mx1,
          and_83_nl);
    end
  end
  always @(posedge clk) begin
    if ( mux_82_nl & (fsm_output[1]) & run_wen & and_179_cse ) begin
      pix_0_lpi_3 <= pix_0_lpi_3_dfm_9_mx1w0;
    end
  end
  always @(posedge clk) begin
    if ( rdbuf1_pix_and_1_cse ) begin
      rdbuf1_pix_lpi_3 <= line_buf1_rsci_q_d;
      rdbuf0_pix_lpi_3 <= line_buf0_rsci_q_d;
    end
  end
  always @(posedge clk) begin
    if ( run_wen & ((~(or_dcpl_40 | (~ VCOL_stage_0_2))) | VCOL_x_and_cse) & (fsm_output[1])
        & (~(mux_16_nl & VCOL_stage_0_1)) ) begin
      pix_7_lpi_3 <= MUX_v_8_2_2(pix_4_lpi_3_dfm_1_mx1, pix_4_lpi_3_dfm_mx0, and_dcpl_23);
    end
  end
  always @(posedge clk) begin
    if ( mux_90_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_6_lpi_3 <= MUX_v_8_2_2(pix_3_lpi_3_dfm_11, pix_6_lpi_3_dfm_9, and_dcpl_23);
    end
  end
  always @(posedge clk) begin
    if ( mux_96_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_8_lpi_3 <= MUX_v_8_2_2(pix_5_lpi_3_dfm_6_mx1, pix_8_lpi_3_dfm_8, and_dcpl_23);
    end
  end
  always @(posedge clk) begin
    if ( mux_103_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_3_lpi_3 <= MUX_v_8_2_2(pix_0_lpi_3_dfm_9_mx1w0, pix_3_lpi_3_dfm_11, and_dcpl_25);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_else_1_else_asn_itm_1 <= 10'b0000000000;
    end
    else if ( rst ) begin
      VCOL_else_1_else_asn_itm_1 <= 10'b0000000000;
    end
    else if ( run_wen & mux_57_cse & and_dcpl_1 ) begin
      VCOL_else_1_else_asn_itm_1 <= VROW_y_sva;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1 <= 1'b0;
    end
    else if ( rst ) begin
      operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1 <= 1'b0;
    end
    else if ( run_wen & (~ mux_tmp_3) & and_dcpl_1 ) begin
      operator_11_false_2_operator_11_false_2_slc_VCOL_x_0_1_itm_1 <= VCOL_x_sva_mx1[0];
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 <= 1'b0;
      VCOL_land_1_lpi_3_dfm_1 <= 1'b0;
      exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 <= 1'b0;
      VCOL_equal_tmp_2_1 <= 1'b0;
      VCOL_equal_tmp_3_1 <= 1'b0;
      VCOL_land_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( rst ) begin
      operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 <= 1'b0;
      VCOL_land_1_lpi_3_dfm_1 <= 1'b0;
      exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 <= 1'b0;
      VCOL_equal_tmp_2_1 <= 1'b0;
      VCOL_equal_tmp_3_1 <= 1'b0;
      VCOL_land_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( operator_10_false_1_and_cse ) begin
      operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 <= operator_10_false_1_operator_10_false_1_and_cse_sva_1;
      VCOL_land_1_lpi_3_dfm_1 <= (VCOL_x_sva_mx1[0]) & operator_11_false_1_nor_tmp
          & operator_10_false_1_operator_10_false_1_and_cse_sva_1;
      exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 <= VCOL_mux_5_nl | VCOL_equal_tmp_4
          | VCOL_equal_tmp_7;
      VCOL_equal_tmp_2_1 <= VCOL_equal_tmp_6;
      VCOL_equal_tmp_3_1 <= VCOL_equal_tmp_7;
      VCOL_land_lpi_3_dfm_1 <= ~(operator_11_false_acc_itm_11_1 | operator_10_false_acc_itm_10_1);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      reg_operator_11_false_6_nor_itm_1_cse <= 1'b0;
      VCOL_and_10_itm_1 <= 1'b0;
      VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1 <= 1'b0;
    end
    else if ( rst ) begin
      reg_operator_11_false_6_nor_itm_1_cse <= 1'b0;
      VCOL_and_10_itm_1 <= 1'b0;
      VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1 <= 1'b0;
    end
    else if ( operator_11_false_6_and_cse ) begin
      reg_operator_11_false_6_nor_itm_1_cse <= operator_11_false_1_nor_tmp;
      VCOL_and_10_itm_1 <= (VCOL_x_sva_mx1[0]) & (~ operator_11_false_1_nor_tmp);
      VCOL_VCOL_oelse_operator_11_false_or_cse_sva_1 <= VCOL_VCOL_oelse_operator_11_false_or_tmp;
    end
  end
  always @(posedge clk) begin
    if ( mux_113_nl & run_wen & (fsm_output[1]) & VCOL_stage_0_2 ) begin
      pix_4_lpi_3 <= MUX_v_8_2_2(pix_1_lpi_3_dfm_9_mx1w0, pix_4_lpi_3_dfm_1_mx1,
          and_dcpl_25);
    end
  end
  always @(posedge clk) begin
    if ( mux_118_nl & (fsm_output[1]) & run_wen & and_179_cse ) begin
      pix_1_lpi_3 <= pix_1_lpi_3_dfm_9_mx1w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_equal_tmp_1 <= 1'b0;
      VCOL_equal_tmp_1_1 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_equal_tmp_1 <= 1'b0;
      VCOL_equal_tmp_1_1 <= 1'b0;
    end
    else if ( VCOL_and_41_cse ) begin
      VCOL_equal_tmp_1 <= VCOL_equal_tmp_4;
      VCOL_equal_tmp_1_1 <= (VCOL_mux_6_cse==2'b01);
    end
  end
  always @(posedge clk) begin
    if ( and_232_cse ) begin
      pix_result_7_4_lpi_3 <= pix_result_7_4_lpi_3_dfm_2_mx0w1;
      pix_result_15_8_lpi_3 <= pix_result_15_8_lpi_3_dfm_2_mx0w1;
      pix_result_3_1_lpi_3 <= pix_result_3_1_lpi_3_dfm_2_mx0w1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( rst ) begin
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( VCOL_else_3_if_for_and_52_cse ) begin
      lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 <= lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_2;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_result_16_lpi_3 <= 1'b0;
    end
    else if ( rst ) begin
      pix_result_16_lpi_3 <= 1'b0;
    end
    else if ( run_wen & VCOL_stage_0_2 & (fsm_output[1]) & (mux_31_nl | (~ VCOL_stage_0_1))
        ) begin
      pix_result_16_lpi_3 <= pix_result_16_lpi_3_dfm_2_mx1w0;
    end
  end
  always @(posedge clk) begin
    if ( VCOL_else_3_if_for_and_52_cse ) begin
      i_1_lpi_3_dfm_1 <= VCOL_VCOL_and_6_cse;
    end
  end
  always @(posedge clk) begin
    if ( pix_result_dy_and_cse ) begin
      pix_result_dy_16_lpi_3 <= VCOL_else_3_else_if_for_1_acc_psp_1_sva_1[17];
      pix_result_dy_0_lpi_3 <= pix_result_dy_0_sva_2;
      pix_result_dx_16_lpi_3 <= z_out_1[17];
      pix_result_dx_0_lpi_3 <= pix_result_dx_0_sva_2;
    end
  end
  always @(posedge clk) begin
    if ( pix_result_dy_and_3_cse ) begin
      pix_result_dy_15_1_lpi_3 <= pix_result_dy_15_1_sva_2;
      pix_result_dx_15_1_lpi_3 <= pix_result_dx_15_1_sva_2;
    end
  end
  always @(posedge clk) begin
    if ( run_wen & (~ mux_36_itm) & VCOL_stage_0_1 ) begin
      VCOL_else_3_else_if_for_1_mux_itm_1 <= MUX_v_3_9_2(3'b001, 3'b010, 3'b001,
          3'b000, 3'b000, 3'b000, 3'b111, 3'b110, 3'b111, i_lpi_3_dfm_2);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_if_4_VCOL_if_4_and_itm_1 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_if_4_VCOL_if_4_and_itm_1 <= 1'b0;
    end
    else if ( run_wen & mux_42_nl & VCOL_stage_0_1 ) begin
      VCOL_if_4_VCOL_if_4_and_itm_1 <= VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1_mx0
          & ((VROW_y_sva!=10'b0000000000));
    end
  end
  always @(posedge clk) begin
    if ( run_wen & mux_48_nl & VCOL_stage_0_1 ) begin
      i_1_lpi_3_dfm_1_1 <= i_1_sva_1_mx0w0;
    end
  end
  always @(posedge clk) begin
    if ( run_wen & (~ mux_36_itm) & VCOL_stage_0_1 & (~ VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp)
        ) begin
      i_lpi_3_dfm_1_1 <= i_sva_2;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1 <= 2'b00;
    end
    else if ( rst ) begin
      VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1 <= 2'b00;
    end
    else if ( mux_119_nl & and_dcpl_74 ) begin
      VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1 <= VCOL_mux_6_cse;
    end
  end
  always @(posedge clk) begin
    if ( or_204_cse & exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 & (~ (fsm_output[2]))
        & run_wen & VCOL_stage_0_2 ) begin
      VCOL_VCOL_slc_pix_39_32_2_lpi_4 <= VCOL_VCOL_slc_pix_39_32_2_lpi_3_dfm_mx1w0;
    end
  end
  always @(posedge clk) begin
    if ( run_wen & (~(or_dcpl_28 | (fsm_output[2]))) & or_dcpl_3 ) begin
      VCOL_VCOL_slc_pix_63_56_lpi_4 <= pix_4_lpi_3_dfm_1_mx1;
    end
  end
  always @(posedge clk) begin
    if ( VCOL_and_38_cse ) begin
      VCOL_VCOL_slc_pix_47_40_2_lpi_4 <= pix_2_lpi_3_dfm_9_mx1w0;
    end
  end
  always @(posedge clk) begin
    if ( VCOL_and_38_cse & or_dcpl_3 ) begin
      VCOL_VCOL_slc_pix_71_64_lpi_4 <= pix_5_lpi_3_dfm_6_mx1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( rst ) begin
      operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( run_wen & mux_65_itm ) begin
      operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1 <= operator_11_false_4_operator_11_false_4_nor_tmp;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1 <= 1'b0;
    end
    else if ( mux_121_nl & and_dcpl_74 ) begin
      VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1 <= VCOL_VCOL_oelse_operator_11_false_or_cse_lpi_3_dfm_1_mx0;
    end
  end
  always @(posedge clk) begin
    if ( mux_124_nl & (fsm_output[1]) & VCOL_stage_0_2 & run_wen ) begin
      pix_result_0_lpi_3 <= pix_result_0_lpi_3_dfm_2_mx1w0;
    end
  end
  assign not_233_nl = ~ VROW_y_or_cse;
  assign VROW_y_not_2_nl = ~ (fsm_output[0]);
  assign VCOL_if_4_nor_1_nl = ~(MUX_v_4_2_2(pix_result_7_4_lpi_3_dfm_2_mx0w1, 4'b1111,
      operator_17_17_true_AC_RND_AC_SAT_acc_itm_8_1));
  assign VCOL_if_4_nor_2_nl = ~(MUX_v_3_2_2(pix_result_3_1_lpi_3_dfm_2_mx0w1, 3'b111,
      operator_17_17_true_AC_RND_AC_SAT_acc_itm_8_1));
  assign mux_nl = MUX_s_1_2_2(and_cse, VCOL_else_2_else_aif_equal_tmp, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign or_188_nl = and_253_cse | VROW_equal_tmp;
  assign mux_71_nl = MUX_s_1_2_2(mux_nl, or_188_nl, reg_operator_11_false_6_nor_itm_1_cse);
  assign or_187_nl = VCOL_else_2_else_aif_equal_tmp | VROW_equal_tmp;
  assign or_186_nl = (VCOL_x_sva!=11'b00000000001);
  assign mux_72_nl = MUX_s_1_2_2(mux_71_nl, or_187_nl, or_186_nl);
  assign and_83_nl = and_dcpl_23 & (fsm_output[1]);
  assign nor_74_nl = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 |
      (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1) | (VCOL_x_sva!=11'b00000000001));
  assign mux_74_nl = MUX_s_1_2_2(exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1, nor_74_nl,
      VCOL_else_2_else_aif_equal_tmp);
  assign or_192_nl = exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1 | reg_operator_11_false_6_nor_itm_1_cse
      | (VCOL_x_sva!=11'b00000000001);
  assign nand_27_nl = ~(operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 &
      nand_37_cse);
  assign mux_73_nl = MUX_s_1_2_2(or_192_nl, nand_27_nl, VCOL_else_2_else_aif_equal_tmp);
  assign mux_75_nl = MUX_s_1_2_2(mux_74_nl, mux_73_nl, VROW_equal_tmp);
  assign or_190_nl = (~ exitL_exitL_exit_VCOL_else_3_if_for_1_sva) | VCOL_land_1_lpi_3_dfm_1;
  assign mux_76_nl = MUX_s_1_2_2(mux_75_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1,
      or_190_nl);
  assign and_256_nl = nand_39_cse & mux_tmp_79;
  assign mux_81_nl = MUX_s_1_2_2(and_256_nl, nand_tmp_4, VCOL_else_2_else_aif_equal_tmp);
  assign mux_80_nl = MUX_s_1_2_2(mux_tmp_79, nand_tmp_4, VCOL_else_2_else_aif_equal_tmp);
  assign nor_54_nl = ~((~((VROW_y_sva!=10'b0000000001))) | (VCOL_x_sva_2!=11'b00000000001));
  assign mux_82_nl = MUX_s_1_2_2(mux_81_nl, mux_80_nl, nor_54_nl);
  assign or_27_nl = ((VCOL_x_sva[0]) & (VROW_y_sva[0]) & operator_10_false_1_nor_tmp
      & operator_11_false_1_nor_tmp) | mux_tmp_10;
  assign mux_15_nl = MUX_s_1_2_2(mux_tmp_10, or_27_nl, exitL_exitL_exit_VCOL_else_3_if_for_1_sva);
  assign mux_11_nl = MUX_s_1_2_2((~ (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1])),
      (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]), VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign nor_23_nl = ~(VCOL_else_2_else_aif_equal_tmp | (~((VCOL_else_3_if_for_mux_46_tmp_0
      & (VROW_y_sva[0]) & operator_10_false_1_nor_tmp & operator_11_false_1_nor_tmp)
      | mux_tmp_10)));
  assign mux_12_nl = MUX_s_1_2_2(mux_11_nl, nor_23_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign mux_16_nl = MUX_s_1_2_2(mux_15_nl, mux_12_nl, VCOL_stage_0_2);
  assign nor_76_nl = ~(VCOL_stage_0_1 | (~ or_tmp_156));
  assign mux_88_nl = MUX_s_1_2_2(nor_76_nl, or_tmp_156, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign and_258_nl = nand_41_cse & or_tmp_156;
  assign mux_89_nl = MUX_s_1_2_2(mux_88_nl, and_258_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign and_259_nl = exitL_exitL_exit_VCOL_else_3_if_for_1_sva & mux_89_nl;
  assign mux_90_nl = MUX_s_1_2_2(and_259_nl, mux_84_cse, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign nor_77_nl = ~(VCOL_stage_0_1 | (~ or_tmp_165));
  assign mux_94_nl = MUX_s_1_2_2(nor_77_nl, or_tmp_165, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]);
  assign and_261_nl = nand_41_cse & or_tmp_165;
  assign mux_95_nl = MUX_s_1_2_2(mux_94_nl, and_261_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign and_262_nl = exitL_exitL_exit_VCOL_else_3_if_for_1_sva & mux_95_nl;
  assign mux_96_nl = MUX_s_1_2_2(and_262_nl, mux_84_cse, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign and_219_nl = exitL_exitL_exit_VCOL_else_3_if_for_1_sva & (or_tmp_169 | (operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & (~(nor_78_cse | VROW_equal_tmp))));
  assign and_264_nl = operator_10_false_1_operator_10_false_1_and_cse_sva_1_1 & (~(nor_78_cse
      | VROW_equal_tmp | (~ mux_tmp_99)));
  assign mux_100_nl = MUX_s_1_2_2(and_264_nl, mux_tmp_99, or_tmp_169);
  assign and_218_nl = exitL_exitL_exit_VCOL_else_3_if_for_1_sva & mux_100_nl;
  assign mux_101_nl = MUX_s_1_2_2(mux_tmp_99, and_218_nl, operator_11_false_4_operator_11_false_4_nor_cse_lpi_3_dfm_1);
  assign mux_102_nl = MUX_s_1_2_2(and_219_nl, mux_101_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign or_227_nl = (~ VROW_equal_tmp) | reg_operator_11_false_6_nor_itm_1_cse;
  assign and_265_nl = VROW_equal_tmp & reg_operator_11_false_6_nor_itm_1_cse;
  assign mux_97_nl = MUX_s_1_2_2(or_227_nl, and_265_nl, or_226_cse);
  assign or_228_nl = (~ exitL_exitL_exit_VCOL_else_3_if_for_1_sva) | operator_11_false_4_operator_11_false_4_nor_cse_sva_1
      | VCOL_land_1_lpi_3_dfm_1 | operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      | ((VCOL_x_sva[0]) & mux_97_nl);
  assign and_216_nl = exitL_exitL_exit_VCOL_else_3_if_for_1_sva & (or_tmp_169 | (operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      & (~((VCOL_x_sva[0]) & VROW_equal_tmp & reg_operator_11_false_6_nor_itm_1_cse))));
  assign mux_98_nl = MUX_s_1_2_2(or_228_nl, and_216_nl, or_222_cse);
  assign mux_103_nl = MUX_s_1_2_2(mux_102_nl, mux_98_nl, VCOL_else_2_else_aif_equal_tmp);
  assign VCOL_mux_5_nl = MUX_s_1_2_2((~ operator_4_false_1_acc_itm_3), VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp,
      VCOL_equal_tmp_6);
  assign and_223_nl = ((~ VCOL_stage_0_1) | (VCOL_x_sva_2!=11'b00000000000)) & nand_tmp_11;
  assign mux_107_nl = MUX_s_1_2_2(nand_tmp_11, mux_tmp_104, or_226_cse);
  assign mux_106_nl = MUX_s_1_2_2(mux_tmp_104, nand_tmp_11, reg_operator_11_false_6_nor_itm_1_cse);
  assign mux_108_nl = MUX_s_1_2_2(mux_107_nl, mux_106_nl, VROW_equal_tmp);
  assign mux_109_nl = MUX_s_1_2_2(mux_tmp_104, mux_108_nl, VCOL_x_sva[0]);
  assign mux_105_nl = MUX_s_1_2_2(mux_tmp_104, nand_tmp_11, and_268_cse);
  assign mux_110_nl = MUX_s_1_2_2(mux_109_nl, mux_105_nl, operator_10_false_1_operator_10_false_1_and_cse_sva_1_1);
  assign mux_111_nl = MUX_s_1_2_2(mux_110_nl, nand_tmp_11, VCOL_land_1_lpi_3_dfm_1);
  assign mux_112_nl = MUX_s_1_2_2(and_223_nl, mux_111_nl, VCOL_else_2_else_aif_equal_tmp);
  assign mux_113_nl = MUX_s_1_2_2(VCOL_else_3_if_for_and_5_cse, mux_112_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign mux_116_nl = MUX_s_1_2_2(or_tmp_195, (~ or_tmp_191), VCOL_x_sva_2[0]);
  assign or_248_nl = (VCOL_x_sva_2[10:1]!=10'b0000000000);
  assign mux_117_nl = MUX_s_1_2_2(mux_116_nl, or_tmp_195, or_248_nl);
  assign or_247_nl = (VCOL_x_sva!=11'b00000000001) | operator_10_false_1_operator_10_false_1_and_cse_sva_1_1
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_and_10_itm_1;
  assign or_246_nl = (~ (VCOL_x_sva[0])) | (~ reg_operator_11_false_6_nor_itm_1_cse)
      | operator_11_false_4_operator_11_false_4_nor_cse_sva_1 | VCOL_and_10_itm_1;
  assign mux_114_nl = MUX_s_1_2_2(or_247_nl, or_246_nl, VROW_equal_tmp);
  assign mux_115_nl = MUX_s_1_2_2(mux_114_nl, or_tmp_191, VCOL_land_1_lpi_3_dfm_1);
  assign mux_118_nl = MUX_s_1_2_2((~ mux_117_nl), mux_115_nl, VCOL_else_2_else_aif_equal_tmp);
  assign mux_31_nl = MUX_s_1_2_2((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]),
      or_43_cse, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign mux_41_nl = MUX_s_1_2_2((~ operator_4_false_1_acc_itm_3), mux_tmp_37, or_53_cse);
  assign or_nl = (~ (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1])) | VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp;
  assign or_169_nl = (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) | (~ operator_4_false_1_acc_itm_3);
  assign mux_38_nl = MUX_s_1_2_2(or_nl, or_169_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign nor_34_nl = ~(VCOL_else_2_else_aif_equal_tmp | (~ mux_tmp_37));
  assign mux_39_nl = MUX_s_1_2_2(mux_38_nl, nor_34_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign mux_42_nl = MUX_s_1_2_2(mux_41_nl, mux_39_nl, VCOL_stage_0_2);
  assign mux_47_nl = MUX_s_1_2_2(operator_4_false_1_acc_itm_3, (~ mux_tmp_37), or_53_cse);
  assign nor_27_nl = ~((~ (VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1])) |
      VCOL_else_3_else_if_for_VCOL_else_3_else_if_for_nor_3_tmp);
  assign nor_28_nl = ~((VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[1]) | (~
      operator_4_false_1_acc_itm_3));
  assign mux_44_nl = MUX_s_1_2_2(nor_27_nl, nor_28_nl, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign nor_29_nl = ~(VCOL_else_2_else_aif_equal_tmp | mux_tmp_37);
  assign mux_45_nl = MUX_s_1_2_2(mux_44_nl, nor_29_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign mux_48_nl = MUX_s_1_2_2(mux_47_nl, mux_45_nl, VCOL_stage_0_2);
  assign nor_83_nl = ~(VCOL_else_2_else_aif_equal_tmp | (~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1));
  assign mux_119_nl = MUX_s_1_2_2(or_53_cse, nor_83_nl, VCOL_stage_0_2);
  assign and_269_nl = exitL_exitL_exit_VCOL_else_3_if_for_1_sva & (~ mux_tmp_120);
  assign nor_84_nl = ~((~ exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1) | VCOL_else_2_else_aif_equal_tmp
      | mux_tmp_120);
  assign mux_121_nl = MUX_s_1_2_2(and_269_nl, nor_84_nl, VCOL_stage_0_2);
  assign mux_123_nl = MUX_s_1_2_2(not_tmp_125, or_251_cse, VCOL_io_read_ctrl_signal_rsc_sft_lpi_3_dfm_st_1[0]);
  assign mux_122_nl = MUX_s_1_2_2(not_tmp_125, or_251_cse, or_43_cse);
  assign mux_124_nl = MUX_s_1_2_2(mux_123_nl, mux_122_nl, exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign VROW_or_2_nl = (mux_tmp & (fsm_output[1])) | or_tmp_129;
  assign VROW_VROW_mux_1_nl = MUX_v_10_2_2(VROW_y_sva, (VCOL_x_sva_mx1[10:1]), VROW_or_2_nl);
  assign nl_z_out = VROW_VROW_mux_1_nl + conv_s2u_2_10({or_tmp_129 , 1'b1});
  assign z_out = nl_z_out[9:0];
  assign VCOL_VCOL_and_18_nl = pix_result_dx_16_lpi_3 & lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign VCOL_else_3_if_for_mux_68_nl = MUX_s_1_2_2(exs_tmp_1_12, VCOL_VCOL_and_18_nl,
      or_tmp_131);
  assign VCOL_else_3_if_for_mux_69_nl = MUX_v_4_2_2(({{3{exs_tmp_1_12}}, exs_tmp_1_12}),
      (pix_result_dx_conc_itm_15_1[14:11]), or_tmp_131);
  assign VCOL_VCOL_and_19_nl = MUX_v_8_2_2(8'b00000000, pix_result_15_8_lpi_3, lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1);
  assign VCOL_else_3_if_for_mux_70_nl = MUX_v_8_2_2(VCOL_VCOL_and_19_nl, (pix_result_dx_conc_itm_15_1[10:3]),
      or_tmp_131);
  assign VCOL_else_3_if_for_mux_71_nl = MUX_v_3_2_2((exs_tmp_1_3_0[3:1]), (pix_result_dx_conc_itm_15_1[2:0]),
      or_tmp_131);
  assign VCOL_VCOL_and_20_nl = pix_result_dx_0_lpi_3 & lfst_exitL_exit_VCOL_else_3_if_for_1_lpi_3_dfm_1;
  assign VCOL_else_3_if_for_mux_72_nl = MUX_s_1_2_2((exs_tmp_1_3_0[0]), VCOL_VCOL_and_20_nl,
      or_tmp_131);
  assign VCOL_else_3_if_for_mux_73_nl = MUX_s_1_2_2((z_out_2[10]), (z_out_2[9]),
      or_tmp_131);
  assign nl_z_out_1 = conv_s2u_17_18({VCOL_else_3_if_for_mux_68_nl , VCOL_else_3_if_for_mux_69_nl
      , VCOL_else_3_if_for_mux_70_nl , VCOL_else_3_if_for_mux_71_nl , VCOL_else_3_if_for_mux_72_nl})
      + conv_s2u_11_18({VCOL_else_3_if_for_mux_73_nl , (z_out_2[9:0])});
  assign z_out_1 = nl_z_out_1[17:0];
  assign VCOL_else_3_if_for_mux_74_nl = MUX_v_4_9_2(4'b0000, 4'b1111, 4'b0000, 4'b1111,
      4'b0100, 4'b1111, 4'b0000, 4'b1111, 4'b0000, i_1_lpi_3_dfm_1);
  assign VCOL_else_3_else_if_for_mux_2_nl = MUX_v_3_9_2(3'b001, 3'b000, 3'b111, 3'b010,
      3'b000, 3'b110, 3'b001, 3'b000, 3'b111, i_1_lpi_3_dfm_1);
  assign operator_10_10_true_AC_TRN_AC_SAT_mux_1_nl = MUX_v_4_2_2(VCOL_else_3_if_for_mux_74_nl,
      (signext_4_3(VCOL_else_3_else_if_for_mux_2_nl)), or_tmp_131);
  assign nl_z_out_2 = $signed(operator_10_10_true_AC_TRN_AC_SAT_mux_1_nl) * $signed(conv_u2s_8_9(VCOL_else_3_if_for_mux_61));
  assign z_out_2 = nl_z_out_2[10:0];

  function automatic  MUX1HOT_s_1_3_2;
    input  input_2;
    input  input_1;
    input  input_0;
    input [2:0] sel;
    reg  result;
  begin
    result = input_0 & sel[0];
    result = result | (input_1 & sel[1]);
    result = result | (input_2 & sel[2]);
    MUX1HOT_s_1_3_2 = result;
  end
  endfunction


  function automatic  MUX1HOT_s_1_4_2;
    input  input_3;
    input  input_2;
    input  input_1;
    input  input_0;
    input [3:0] sel;
    reg  result;
  begin
    result = input_0 & sel[0];
    result = result | (input_1 & sel[1]);
    result = result | (input_2 & sel[2]);
    result = result | (input_3 & sel[3]);
    MUX1HOT_s_1_4_2 = result;
  end
  endfunction


  function automatic [2:0] MUX1HOT_v_3_4_2;
    input [2:0] input_3;
    input [2:0] input_2;
    input [2:0] input_1;
    input [2:0] input_0;
    input [3:0] sel;
    reg [2:0] result;
  begin
    result = input_0 & {3{sel[0]}};
    result = result | (input_1 & {3{sel[1]}});
    result = result | (input_2 & {3{sel[2]}});
    result = result | (input_3 & {3{sel[3]}});
    MUX1HOT_v_3_4_2 = result;
  end
  endfunction


  function automatic [3:0] MUX1HOT_v_4_4_2;
    input [3:0] input_3;
    input [3:0] input_2;
    input [3:0] input_1;
    input [3:0] input_0;
    input [3:0] sel;
    reg [3:0] result;
  begin
    result = input_0 & {4{sel[0]}};
    result = result | (input_1 & {4{sel[1]}});
    result = result | (input_2 & {4{sel[2]}});
    result = result | (input_3 & {4{sel[3]}});
    MUX1HOT_v_4_4_2 = result;
  end
  endfunction


  function automatic [7:0] MUX1HOT_v_8_3_2;
    input [7:0] input_2;
    input [7:0] input_1;
    input [7:0] input_0;
    input [2:0] sel;
    reg [7:0] result;
  begin
    result = input_0 & {8{sel[0]}};
    result = result | (input_1 & {8{sel[1]}});
    result = result | (input_2 & {8{sel[2]}});
    MUX1HOT_v_8_3_2 = result;
  end
  endfunction


  function automatic [7:0] MUX1HOT_v_8_4_2;
    input [7:0] input_3;
    input [7:0] input_2;
    input [7:0] input_1;
    input [7:0] input_0;
    input [3:0] sel;
    reg [7:0] result;
  begin
    result = input_0 & {8{sel[0]}};
    result = result | (input_1 & {8{sel[1]}});
    result = result | (input_2 & {8{sel[2]}});
    result = result | (input_3 & {8{sel[3]}});
    MUX1HOT_v_8_4_2 = result;
  end
  endfunction


  function automatic [7:0] MUX1HOT_v_8_5_2;
    input [7:0] input_4;
    input [7:0] input_3;
    input [7:0] input_2;
    input [7:0] input_1;
    input [7:0] input_0;
    input [4:0] sel;
    reg [7:0] result;
  begin
    result = input_0 & {8{sel[0]}};
    result = result | (input_1 & {8{sel[1]}});
    result = result | (input_2 & {8{sel[2]}});
    result = result | (input_3 & {8{sel[3]}});
    result = result | (input_4 & {8{sel[4]}});
    MUX1HOT_v_8_5_2 = result;
  end
  endfunction


  function automatic [7:0] MUX1HOT_v_8_7_2;
    input [7:0] input_6;
    input [7:0] input_5;
    input [7:0] input_4;
    input [7:0] input_3;
    input [7:0] input_2;
    input [7:0] input_1;
    input [7:0] input_0;
    input [6:0] sel;
    reg [7:0] result;
  begin
    result = input_0 & {8{sel[0]}};
    result = result | (input_1 & {8{sel[1]}});
    result = result | (input_2 & {8{sel[2]}});
    result = result | (input_3 & {8{sel[3]}});
    result = result | (input_4 & {8{sel[4]}});
    result = result | (input_5 & {8{sel[5]}});
    result = result | (input_6 & {8{sel[6]}});
    MUX1HOT_v_8_7_2 = result;
  end
  endfunction


  function automatic  MUX_s_1_2_2;
    input  input_0;
    input  input_1;
    input  sel;
    reg  result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_s_1_2_2 = result;
  end
  endfunction


  function automatic [9:0] MUX_v_10_2_2;
    input [9:0] input_0;
    input [9:0] input_1;
    input  sel;
    reg [9:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_10_2_2 = result;
  end
  endfunction


  function automatic [10:0] MUX_v_11_2_2;
    input [10:0] input_0;
    input [10:0] input_1;
    input  sel;
    reg [10:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_11_2_2 = result;
  end
  endfunction


  function automatic [14:0] MUX_v_15_2_2;
    input [14:0] input_0;
    input [14:0] input_1;
    input  sel;
    reg [14:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_15_2_2 = result;
  end
  endfunction


  function automatic [1:0] MUX_v_2_2_2;
    input [1:0] input_0;
    input [1:0] input_1;
    input  sel;
    reg [1:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_2_2_2 = result;
  end
  endfunction


  function automatic [2:0] MUX_v_3_2_2;
    input [2:0] input_0;
    input [2:0] input_1;
    input  sel;
    reg [2:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_3_2_2 = result;
  end
  endfunction


  function automatic [2:0] MUX_v_3_9_2;
    input [2:0] input_0;
    input [2:0] input_1;
    input [2:0] input_2;
    input [2:0] input_3;
    input [2:0] input_4;
    input [2:0] input_5;
    input [2:0] input_6;
    input [2:0] input_7;
    input [2:0] input_8;
    input [3:0] sel;
    reg [2:0] result;
  begin
    case (sel)
      4'b0000 : begin
        result = input_0;
      end
      4'b0001 : begin
        result = input_1;
      end
      4'b0010 : begin
        result = input_2;
      end
      4'b0011 : begin
        result = input_3;
      end
      4'b0100 : begin
        result = input_4;
      end
      4'b0101 : begin
        result = input_5;
      end
      4'b0110 : begin
        result = input_6;
      end
      4'b0111 : begin
        result = input_7;
      end
      default : begin
        result = input_8;
      end
    endcase
    MUX_v_3_9_2 = result;
  end
  endfunction


  function automatic [3:0] MUX_v_4_2_2;
    input [3:0] input_0;
    input [3:0] input_1;
    input  sel;
    reg [3:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_4_2_2 = result;
  end
  endfunction


  function automatic [3:0] MUX_v_4_9_2;
    input [3:0] input_0;
    input [3:0] input_1;
    input [3:0] input_2;
    input [3:0] input_3;
    input [3:0] input_4;
    input [3:0] input_5;
    input [3:0] input_6;
    input [3:0] input_7;
    input [3:0] input_8;
    input [3:0] sel;
    reg [3:0] result;
  begin
    case (sel)
      4'b0000 : begin
        result = input_0;
      end
      4'b0001 : begin
        result = input_1;
      end
      4'b0010 : begin
        result = input_2;
      end
      4'b0011 : begin
        result = input_3;
      end
      4'b0100 : begin
        result = input_4;
      end
      4'b0101 : begin
        result = input_5;
      end
      4'b0110 : begin
        result = input_6;
      end
      4'b0111 : begin
        result = input_7;
      end
      default : begin
        result = input_8;
      end
    endcase
    MUX_v_4_9_2 = result;
  end
  endfunction


  function automatic [7:0] MUX_v_8_2_2;
    input [7:0] input_0;
    input [7:0] input_1;
    input  sel;
    reg [7:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_8_2_2 = result;
  end
  endfunction


  function automatic [7:0] MUX_v_8_9_2;
    input [7:0] input_0;
    input [7:0] input_1;
    input [7:0] input_2;
    input [7:0] input_3;
    input [7:0] input_4;
    input [7:0] input_5;
    input [7:0] input_6;
    input [7:0] input_7;
    input [7:0] input_8;
    input [3:0] sel;
    reg [7:0] result;
  begin
    case (sel)
      4'b0000 : begin
        result = input_0;
      end
      4'b0001 : begin
        result = input_1;
      end
      4'b0010 : begin
        result = input_2;
      end
      4'b0011 : begin
        result = input_3;
      end
      4'b0100 : begin
        result = input_4;
      end
      4'b0101 : begin
        result = input_5;
      end
      4'b0110 : begin
        result = input_6;
      end
      4'b0111 : begin
        result = input_7;
      end
      default : begin
        result = input_8;
      end
    endcase
    MUX_v_8_9_2 = result;
  end
  endfunction


  function automatic [0:0] readslicef_11_1_10;
    input [10:0] vector;
    reg [10:0] tmp;
  begin
    tmp = vector >> 10;
    readslicef_11_1_10 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_12_1_11;
    input [11:0] vector;
    reg [11:0] tmp;
  begin
    tmp = vector >> 11;
    readslicef_12_1_11 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_4_1_3;
    input [3:0] vector;
    reg [3:0] tmp;
  begin
    tmp = vector >> 3;
    readslicef_4_1_3 = tmp[0:0];
  end
  endfunction


  function automatic [0:0] readslicef_9_1_8;
    input [8:0] vector;
    reg [8:0] tmp;
  begin
    tmp = vector >> 8;
    readslicef_9_1_8 = tmp[0:0];
  end
  endfunction


  function automatic [3:0] signext_4_3;
    input [2:0] vector;
  begin
    signext_4_3= {{1{vector[2]}}, vector};
  end
  endfunction


  function automatic [17:0] conv_s2s_10_18 ;
    input [9:0]  vector ;
  begin
    conv_s2s_10_18 = {{8{vector[9]}}, vector};
  end
  endfunction


  function automatic [17:0] conv_s2s_17_18 ;
    input [16:0]  vector ;
  begin
    conv_s2s_17_18 = {vector[16], vector};
  end
  endfunction


  function automatic [9:0] conv_s2u_2_10 ;
    input [1:0]  vector ;
  begin
    conv_s2u_2_10 = {{8{vector[1]}}, vector};
  end
  endfunction


  function automatic [17:0] conv_s2u_11_18 ;
    input [10:0]  vector ;
  begin
    conv_s2u_11_18 = {{7{vector[10]}}, vector};
  end
  endfunction


  function automatic [17:0] conv_s2u_17_18 ;
    input [16:0]  vector ;
  begin
    conv_s2u_17_18 = {vector[16], vector};
  end
  endfunction


  function automatic [8:0] conv_u2s_8_9 ;
    input [7:0]  vector ;
  begin
    conv_u2s_8_9 =  {1'b0, vector};
  end
  endfunction


  function automatic [10:0] conv_u2s_10_11 ;
    input [9:0]  vector ;
  begin
    conv_u2s_10_11 =  {1'b0, vector};
  end
  endfunction


  function automatic [11:0] conv_u2s_11_12 ;
    input [10:0]  vector ;
  begin
    conv_u2s_11_12 =  {1'b0, vector};
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_Denoise_IP
// ------------------------------------------------------------------


module EdgeDetect_IP_Denoise_IP (
  clk, rst, arst_n, dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, widthIn, heightIn,
      dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy, ctrl_signal_rsc_dat, ctrl_signal_triosy_lz,
      line_buf0_rsc_en, line_buf0_rsc_q, line_buf0_rsc_we, line_buf0_rsc_d, line_buf0_rsc_adr,
      line_buf1_rsc_en, line_buf1_rsc_q, line_buf1_rsc_we, line_buf1_rsc_d, line_buf1_rsc_adr
);
  input clk;
  input rst;
  input arst_n;
  input [7:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input [10:0] widthIn;
  input [9:0] heightIn;
  output [7:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  input [1:0] ctrl_signal_rsc_dat;
  output ctrl_signal_triosy_lz;
  output line_buf0_rsc_en;
  input [15:0] line_buf0_rsc_q;
  output line_buf0_rsc_we;
  output [15:0] line_buf0_rsc_d;
  output [9:0] line_buf0_rsc_adr;
  output line_buf1_rsc_en;
  input [15:0] line_buf1_rsc_q;
  output line_buf1_rsc_we;
  output [15:0] line_buf1_rsc_d;
  output [9:0] line_buf1_rsc_adr;


  // Interconnect Declarations
  wire [1:0] ctrl_signal_rsci_idat;
  wire [15:0] line_buf0_rsci_d_d;
  wire line_buf0_rsci_en_d;
  wire [15:0] line_buf0_rsci_q_d;
  wire [15:0] line_buf1_rsci_d_d;
  wire line_buf1_rsci_en_d;
  wire [15:0] line_buf1_rsci_q_d;
  wire [9:0] line_buf0_rsci_adr_d_iff;
  wire line_buf0_rsci_we_d_iff;
  wire line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_iff;
  wire line_buf1_rsci_we_d_iff;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_v1 #(.rscid(32'sd5),
  .width(32'sd2)) ctrl_signal_rsci (
      .dat(ctrl_signal_rsc_dat),
      .idat(ctrl_signal_rsci_idat)
    );
  EdgeDetect_IP_Denoise_IP_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_6_16_10_648_648_16_5_gen
      line_buf0_rsci (
      .en(line_buf0_rsc_en),
      .q(line_buf0_rsc_q),
      .we(line_buf0_rsc_we),
      .d(line_buf0_rsc_d),
      .adr(line_buf0_rsc_adr),
      .adr_d(line_buf0_rsci_adr_d_iff),
      .d_d(line_buf0_rsci_d_d),
      .en_d(line_buf0_rsci_en_d),
      .we_d(line_buf0_rsci_we_d_iff),
      .q_d(line_buf0_rsci_q_d),
      .port_0_rw_ram_ir_internal_RMASK_B_d(line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_iff),
      .port_0_rw_ram_ir_internal_WMASK_B_d(line_buf0_rsci_we_d_iff)
    );
  EdgeDetect_IP_Denoise_IP_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_7_16_10_648_648_16_5_gen
      line_buf1_rsci (
      .en(line_buf1_rsc_en),
      .q(line_buf1_rsc_q),
      .we(line_buf1_rsc_we),
      .d(line_buf1_rsc_d),
      .adr(line_buf1_rsc_adr),
      .adr_d(line_buf0_rsci_adr_d_iff),
      .d_d(line_buf1_rsci_d_d),
      .en_d(line_buf1_rsci_en_d),
      .we_d(line_buf1_rsci_we_d_iff),
      .q_d(line_buf1_rsci_q_d),
      .port_0_rw_ram_ir_internal_RMASK_B_d(line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_iff),
      .port_0_rw_ram_ir_internal_WMASK_B_d(line_buf1_rsci_we_d_iff)
    );
  EdgeDetect_IP_Denoise_IP_run EdgeDetect_IP_Denoise_IP_run_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_in_rsc_dat(dat_in_rsc_dat),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .dat_out_rsc_dat(dat_out_rsc_dat),
      .dat_out_rsc_vld(dat_out_rsc_vld),
      .dat_out_rsc_rdy(dat_out_rsc_rdy),
      .ctrl_signal_triosy_lz(ctrl_signal_triosy_lz),
      .ctrl_signal_rsci_idat(ctrl_signal_rsci_idat),
      .line_buf0_rsci_d_d(line_buf0_rsci_d_d),
      .line_buf0_rsci_en_d(line_buf0_rsci_en_d),
      .line_buf0_rsci_q_d(line_buf0_rsci_q_d),
      .line_buf1_rsci_d_d(line_buf1_rsci_d_d),
      .line_buf1_rsci_en_d(line_buf1_rsci_en_d),
      .line_buf1_rsci_q_d(line_buf1_rsci_q_d),
      .line_buf0_rsci_adr_d_pff(line_buf0_rsci_adr_d_iff),
      .line_buf0_rsci_we_d_pff(line_buf0_rsci_we_d_iff),
      .line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_pff(line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_iff),
      .line_buf1_rsci_we_d_pff(line_buf1_rsci_we_d_iff)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Filter
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Filter (
  clk, rst, arst_n, dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, widthIn, heightIn,
      dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy, ctrl_signal_rsc_dat, ctrl_signal_triosy_lz,
      line_buf0_rsc_en, line_buf0_rsc_q, line_buf0_rsc_we, line_buf0_rsc_d, line_buf0_rsc_adr,
      line_buf1_rsc_en, line_buf1_rsc_q, line_buf1_rsc_we, line_buf1_rsc_d, line_buf1_rsc_adr
);
  input clk;
  input rst;
  input arst_n;
  input [7:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input [10:0] widthIn;
  input [9:0] heightIn;
  output [7:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  input [1:0] ctrl_signal_rsc_dat;
  output ctrl_signal_triosy_lz;
  output line_buf0_rsc_en;
  input [15:0] line_buf0_rsc_q;
  output line_buf0_rsc_we;
  output [15:0] line_buf0_rsc_d;
  output [9:0] line_buf0_rsc_adr;
  output line_buf1_rsc_en;
  input [15:0] line_buf1_rsc_q;
  output line_buf1_rsc_we;
  output [15:0] line_buf1_rsc_d;
  output [9:0] line_buf1_rsc_adr;


  // Interconnect Declarations
  wire [1:0] ctrl_signal_rsci_idat;
  wire [9:0] line_buf0_rsci_adr_d;
  wire [15:0] line_buf0_rsci_d_d;
  wire line_buf0_rsci_en_d;
  wire [15:0] line_buf0_rsci_q_d;
  wire [9:0] line_buf1_rsci_adr_d;
  wire [15:0] line_buf1_rsci_d_d;
  wire line_buf1_rsci_en_d;
  wire [15:0] line_buf1_rsci_q_d;
  wire line_buf0_rsci_we_d_iff;
  wire line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_iff;
  wire line_buf1_rsci_we_d_iff;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_v1 #(.rscid(32'sd15),
  .width(32'sd2)) ctrl_signal_rsci (
      .dat(ctrl_signal_rsc_dat),
      .idat(ctrl_signal_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_Filter_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_16_16_10_648_648_16_5_gen
      line_buf0_rsci (
      .en(line_buf0_rsc_en),
      .q(line_buf0_rsc_q),
      .we(line_buf0_rsc_we),
      .d(line_buf0_rsc_d),
      .adr(line_buf0_rsc_adr),
      .adr_d(line_buf0_rsci_adr_d),
      .d_d(line_buf0_rsci_d_d),
      .en_d(line_buf0_rsci_en_d),
      .we_d(line_buf0_rsci_we_d_iff),
      .q_d(line_buf0_rsci_q_d),
      .port_0_rw_ram_ir_internal_RMASK_B_d(line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_iff),
      .port_0_rw_ram_ir_internal_WMASK_B_d(line_buf0_rsci_we_d_iff)
    );
  EdgeDetect_IP_EdgeDetect_Filter_ccs_sample_mem_ccs_ram_sync_singleport_rwport_en_17_16_10_648_648_16_5_gen
      line_buf1_rsci (
      .en(line_buf1_rsc_en),
      .q(line_buf1_rsc_q),
      .we(line_buf1_rsc_we),
      .d(line_buf1_rsc_d),
      .adr(line_buf1_rsc_adr),
      .adr_d(line_buf1_rsci_adr_d),
      .d_d(line_buf1_rsci_d_d),
      .en_d(line_buf1_rsci_en_d),
      .we_d(line_buf1_rsci_we_d_iff),
      .q_d(line_buf1_rsci_q_d),
      .port_0_rw_ram_ir_internal_RMASK_B_d(line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_iff),
      .port_0_rw_ram_ir_internal_WMASK_B_d(line_buf1_rsci_we_d_iff)
    );
  EdgeDetect_IP_EdgeDetect_Filter_run EdgeDetect_IP_EdgeDetect_Filter_run_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_in_rsc_dat(dat_in_rsc_dat),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .dat_out_rsc_dat(dat_out_rsc_dat),
      .dat_out_rsc_vld(dat_out_rsc_vld),
      .dat_out_rsc_rdy(dat_out_rsc_rdy),
      .ctrl_signal_triosy_lz(ctrl_signal_triosy_lz),
      .ctrl_signal_rsci_idat(ctrl_signal_rsci_idat),
      .line_buf0_rsci_adr_d(line_buf0_rsci_adr_d),
      .line_buf0_rsci_d_d(line_buf0_rsci_d_d),
      .line_buf0_rsci_en_d(line_buf0_rsci_en_d),
      .line_buf0_rsci_q_d(line_buf0_rsci_q_d),
      .line_buf1_rsci_adr_d(line_buf1_rsci_adr_d),
      .line_buf1_rsci_d_d(line_buf1_rsci_d_d),
      .line_buf1_rsci_en_d(line_buf1_rsci_en_d),
      .line_buf1_rsci_q_d(line_buf1_rsci_q_d),
      .line_buf0_rsci_we_d_pff(line_buf0_rsci_we_d_iff),
      .line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_pff(line_buf0_rsci_port_0_rw_ram_ir_internal_RMASK_B_d_iff),
      .line_buf1_rsci_we_d_pff(line_buf1_rsci_we_d_iff)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Top
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Top (
  clk, rst, arst_n, dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, widthIn, heightIn,
      dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy, ctrl_denoise_rsc_dat, ctrl_denoise_triosy_lz,
      ctrl_edgedect_rsc_dat, ctrl_edgedect_triosy_lz, line_buf0_rsc_Denoise_inst_en,
      line_buf0_rsc_Denoise_inst_q, line_buf0_rsc_Denoise_inst_we, line_buf0_rsc_Denoise_inst_d,
      line_buf0_rsc_Denoise_inst_adr, line_buf1_rsc_Denoise_inst_en, line_buf1_rsc_Denoise_inst_q,
      line_buf1_rsc_Denoise_inst_we, line_buf1_rsc_Denoise_inst_d, line_buf1_rsc_Denoise_inst_adr,
      line_buf0_rsc_EdgeDetect_Filter_inst_en, line_buf0_rsc_EdgeDetect_Filter_inst_q,
      line_buf0_rsc_EdgeDetect_Filter_inst_we, line_buf0_rsc_EdgeDetect_Filter_inst_d,
      line_buf0_rsc_EdgeDetect_Filter_inst_adr, line_buf1_rsc_EdgeDetect_Filter_inst_en,
      line_buf1_rsc_EdgeDetect_Filter_inst_q, line_buf1_rsc_EdgeDetect_Filter_inst_we,
      line_buf1_rsc_EdgeDetect_Filter_inst_d, line_buf1_rsc_EdgeDetect_Filter_inst_adr
);
  input clk;
  input rst;
  input arst_n;
  input [7:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input [10:0] widthIn;
  input [9:0] heightIn;
  output [7:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  input [1:0] ctrl_denoise_rsc_dat;
  output ctrl_denoise_triosy_lz;
  input [1:0] ctrl_edgedect_rsc_dat;
  output ctrl_edgedect_triosy_lz;
  output line_buf0_rsc_Denoise_inst_en;
  input [15:0] line_buf0_rsc_Denoise_inst_q;
  output line_buf0_rsc_Denoise_inst_we;
  output [15:0] line_buf0_rsc_Denoise_inst_d;
  output [9:0] line_buf0_rsc_Denoise_inst_adr;
  output line_buf1_rsc_Denoise_inst_en;
  input [15:0] line_buf1_rsc_Denoise_inst_q;
  output line_buf1_rsc_Denoise_inst_we;
  output [15:0] line_buf1_rsc_Denoise_inst_d;
  output [9:0] line_buf1_rsc_Denoise_inst_adr;
  output line_buf0_rsc_EdgeDetect_Filter_inst_en;
  input [15:0] line_buf0_rsc_EdgeDetect_Filter_inst_q;
  output line_buf0_rsc_EdgeDetect_Filter_inst_we;
  output [15:0] line_buf0_rsc_EdgeDetect_Filter_inst_d;
  output [9:0] line_buf0_rsc_EdgeDetect_Filter_inst_adr;
  output line_buf1_rsc_EdgeDetect_Filter_inst_en;
  input [15:0] line_buf1_rsc_EdgeDetect_Filter_inst_q;
  output line_buf1_rsc_EdgeDetect_Filter_inst_we;
  output [15:0] line_buf1_rsc_EdgeDetect_Filter_inst_d;
  output [9:0] line_buf1_rsc_EdgeDetect_Filter_inst_adr;


  // Interconnect Declarations
  wire [7:0] dat_out_rsc_dat_n_Denoise_inst;
  wire dat_out_rsc_rdy_n_Denoise_inst;
  wire line_buf0_rsc_en_n_Denoise_inst;
  wire [15:0] line_buf0_rsc_d_n_Denoise_inst;
  wire [9:0] line_buf0_rsc_adr_n_Denoise_inst;
  wire line_buf1_rsc_en_n_Denoise_inst;
  wire [15:0] line_buf1_rsc_d_n_Denoise_inst;
  wire [9:0] line_buf1_rsc_adr_n_Denoise_inst;
  wire [7:0] dat_in_rsc_dat_n_EdgeDetect_Filter_inst;
  wire dat_in_rsc_vld_n_EdgeDetect_Filter_inst;
  wire [7:0] dat_out_rsc_dat_n_EdgeDetect_Filter_inst;
  wire line_buf0_rsc_en_n_EdgeDetect_Filter_inst;
  wire [15:0] line_buf0_rsc_d_n_EdgeDetect_Filter_inst;
  wire [9:0] line_buf0_rsc_adr_n_EdgeDetect_Filter_inst;
  wire line_buf1_rsc_en_n_EdgeDetect_Filter_inst;
  wire [15:0] line_buf1_rsc_d_n_EdgeDetect_Filter_inst;
  wire [9:0] line_buf1_rsc_adr_n_EdgeDetect_Filter_inst;
  wire dat_in_rsc_rdy_n_Denoise_inst_bud;
  wire dat_out_rsc_vld_n_Denoise_inst_bud;
  wire dat_in_rsc_rdy_n_EdgeDetect_Filter_inst_bud;
  wire ctrl_signal_triosy_lz_n_Denoise_inst_bud;
  wire line_buf0_rsc_we_n_Denoise_inst_bud;
  wire line_buf1_rsc_we_n_Denoise_inst_bud;
  wire dat_out_rsc_vld_n_EdgeDetect_Filter_inst_bud;
  wire ctrl_signal_triosy_lz_n_EdgeDetect_Filter_inst_bud;
  wire line_buf0_rsc_we_n_EdgeDetect_Filter_inst_bud;
  wire line_buf1_rsc_we_n_EdgeDetect_Filter_inst_bud;
  wire dat_noise_out_unc_1;
  wire dat_noise_out_idle;


  // Interconnect Declarations for Component Instantiations 
  ccs_pipe_v6 #(.rscid(32'sd28),
  .width(32'sd8),
  .sz_width(32'sd1),
  .fifo_sz(32'sd2),
  .log2_sz(32'sd1),
  .ph_clk(32'sd1),
  .ph_en(32'sd0),
  .ph_arst(32'sd0),
  .ph_srst(32'sd1)) dat_noise_out_cns_pipe (
      .clk(clk),
      .en(1'b0),
      .arst(arst_n),
      .srst(rst),
      .din_rdy(dat_out_rsc_rdy_n_Denoise_inst),
      .din_vld(dat_out_rsc_vld_n_Denoise_inst_bud),
      .din(dat_out_rsc_dat_n_Denoise_inst),
      .dout_rdy(dat_in_rsc_rdy_n_EdgeDetect_Filter_inst_bud),
      .dout_vld(dat_in_rsc_vld_n_EdgeDetect_Filter_inst),
      .dout(dat_in_rsc_dat_n_EdgeDetect_Filter_inst),
      .sz(dat_noise_out_unc_1),
      .sz_req(1'b0),
      .is_idle(dat_noise_out_idle)
    );
  EdgeDetect_IP_Denoise_IP Denoise_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_in_rsc_dat(dat_in_rsc_dat),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy_n_Denoise_inst_bud),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .dat_out_rsc_dat(dat_out_rsc_dat_n_Denoise_inst),
      .dat_out_rsc_vld(dat_out_rsc_vld_n_Denoise_inst_bud),
      .dat_out_rsc_rdy(dat_out_rsc_rdy_n_Denoise_inst),
      .ctrl_signal_rsc_dat(ctrl_denoise_rsc_dat),
      .ctrl_signal_triosy_lz(ctrl_signal_triosy_lz_n_Denoise_inst_bud),
      .line_buf0_rsc_en(line_buf0_rsc_en_n_Denoise_inst),
      .line_buf0_rsc_q(line_buf0_rsc_Denoise_inst_q),
      .line_buf0_rsc_we(line_buf0_rsc_we_n_Denoise_inst_bud),
      .line_buf0_rsc_d(line_buf0_rsc_d_n_Denoise_inst),
      .line_buf0_rsc_adr(line_buf0_rsc_adr_n_Denoise_inst),
      .line_buf1_rsc_en(line_buf1_rsc_en_n_Denoise_inst),
      .line_buf1_rsc_q(line_buf1_rsc_Denoise_inst_q),
      .line_buf1_rsc_we(line_buf1_rsc_we_n_Denoise_inst_bud),
      .line_buf1_rsc_d(line_buf1_rsc_d_n_Denoise_inst),
      .line_buf1_rsc_adr(line_buf1_rsc_adr_n_Denoise_inst)
    );
  EdgeDetect_IP_EdgeDetect_Filter EdgeDetect_Filter_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_in_rsc_dat(dat_in_rsc_dat_n_EdgeDetect_Filter_inst),
      .dat_in_rsc_vld(dat_in_rsc_vld_n_EdgeDetect_Filter_inst),
      .dat_in_rsc_rdy(dat_in_rsc_rdy_n_EdgeDetect_Filter_inst_bud),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .dat_out_rsc_dat(dat_out_rsc_dat_n_EdgeDetect_Filter_inst),
      .dat_out_rsc_vld(dat_out_rsc_vld_n_EdgeDetect_Filter_inst_bud),
      .dat_out_rsc_rdy(dat_out_rsc_rdy),
      .ctrl_signal_rsc_dat(ctrl_edgedect_rsc_dat),
      .ctrl_signal_triosy_lz(ctrl_signal_triosy_lz_n_EdgeDetect_Filter_inst_bud),
      .line_buf0_rsc_en(line_buf0_rsc_en_n_EdgeDetect_Filter_inst),
      .line_buf0_rsc_q(line_buf0_rsc_EdgeDetect_Filter_inst_q),
      .line_buf0_rsc_we(line_buf0_rsc_we_n_EdgeDetect_Filter_inst_bud),
      .line_buf0_rsc_d(line_buf0_rsc_d_n_EdgeDetect_Filter_inst),
      .line_buf0_rsc_adr(line_buf0_rsc_adr_n_EdgeDetect_Filter_inst),
      .line_buf1_rsc_en(line_buf1_rsc_en_n_EdgeDetect_Filter_inst),
      .line_buf1_rsc_q(line_buf1_rsc_EdgeDetect_Filter_inst_q),
      .line_buf1_rsc_we(line_buf1_rsc_we_n_EdgeDetect_Filter_inst_bud),
      .line_buf1_rsc_d(line_buf1_rsc_d_n_EdgeDetect_Filter_inst),
      .line_buf1_rsc_adr(line_buf1_rsc_adr_n_EdgeDetect_Filter_inst)
    );
  assign dat_in_rsc_rdy = dat_in_rsc_rdy_n_Denoise_inst_bud;
  assign ctrl_denoise_triosy_lz = ctrl_signal_triosy_lz_n_Denoise_inst_bud;
  assign line_buf0_rsc_Denoise_inst_en = line_buf0_rsc_en_n_Denoise_inst;
  assign line_buf0_rsc_Denoise_inst_we = line_buf0_rsc_we_n_Denoise_inst_bud;
  assign line_buf0_rsc_Denoise_inst_d = line_buf0_rsc_d_n_Denoise_inst;
  assign line_buf0_rsc_Denoise_inst_adr = line_buf0_rsc_adr_n_Denoise_inst;
  assign line_buf1_rsc_Denoise_inst_en = line_buf1_rsc_en_n_Denoise_inst;
  assign line_buf1_rsc_Denoise_inst_we = line_buf1_rsc_we_n_Denoise_inst_bud;
  assign line_buf1_rsc_Denoise_inst_d = line_buf1_rsc_d_n_Denoise_inst;
  assign line_buf1_rsc_Denoise_inst_adr = line_buf1_rsc_adr_n_Denoise_inst;
  assign dat_out_rsc_vld = dat_out_rsc_vld_n_EdgeDetect_Filter_inst_bud;
  assign dat_out_rsc_dat = dat_out_rsc_dat_n_EdgeDetect_Filter_inst;
  assign ctrl_edgedect_triosy_lz = ctrl_signal_triosy_lz_n_EdgeDetect_Filter_inst_bud;
  assign line_buf0_rsc_EdgeDetect_Filter_inst_en = line_buf0_rsc_en_n_EdgeDetect_Filter_inst;
  assign line_buf0_rsc_EdgeDetect_Filter_inst_we = line_buf0_rsc_we_n_EdgeDetect_Filter_inst_bud;
  assign line_buf0_rsc_EdgeDetect_Filter_inst_d = line_buf0_rsc_d_n_EdgeDetect_Filter_inst;
  assign line_buf0_rsc_EdgeDetect_Filter_inst_adr = line_buf0_rsc_adr_n_EdgeDetect_Filter_inst;
  assign line_buf1_rsc_EdgeDetect_Filter_inst_en = line_buf1_rsc_en_n_EdgeDetect_Filter_inst;
  assign line_buf1_rsc_EdgeDetect_Filter_inst_we = line_buf1_rsc_we_n_EdgeDetect_Filter_inst_bud;
  assign line_buf1_rsc_EdgeDetect_Filter_inst_d = line_buf1_rsc_d_n_EdgeDetect_Filter_inst;
  assign line_buf1_rsc_EdgeDetect_Filter_inst_adr = line_buf1_rsc_adr_n_EdgeDetect_Filter_inst;
endmodule



