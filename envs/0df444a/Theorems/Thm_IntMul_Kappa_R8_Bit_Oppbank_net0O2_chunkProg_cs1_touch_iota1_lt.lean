-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_chunkProg_cs1_touch_iota1_lt
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_chunkProg_cs1_touch_iota1_lt
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:48:57.634012+00:00
-- url     : https://prove2.me/theorems/1be151c7-8471-4c6a-b8c8-7cabf1df5910
-- title:
--   Touched wires of stage-one chunkProg lie in the iota1-image below NL
-- statement:
--   Every wire touched by the stage-one chunk program \(\mathrm{chunkProg}(\iota_1(b),\,e_1(b),\,\mathrm{cs1})\) is the image under the bank embedding \(\iota_1(b,\cdot)\) of some local index strictly below \(NL=31359\).
--
--   Formally, for \(b<1771\),
--   $$
--   \exists\, \ell < NL,\qquad w = \iota_1(b,\ell).
--   $$
--
--   This is the chunk half of \(\mathrm{net0O2\_blk1\_touch\_iota1\_lt}\); exit edges are elementary from \(\mathrm{range}'(w_{\mathrm{Ent}},NR)\subset[0,NL)\).
--
--   Formalization Note. Structural extraction of the local index uses \(\mathrm{chunkInstrs}\) (edges \(\iota(mv.1)\), XOR gates on \(\{\iota p.1,\iota p.2\}\)); the bound is \(\mathrm{net0O2\_cs1\_locals\_lt\_NL}\).
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: chunkProg touch companion

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (Instr)
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NL)
theorem net0O2_chunkProg_cs1_touch_iota1_lt {ch : Ch} {b : ℕ} (hb : b < 1771)
    (w : Wr)
    (hw : ∃ instr ∈ chunkProg (ι1 b) (ch.e1 b) cs1,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ∃ ℓ < NL, w = ι1 b ℓ := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
