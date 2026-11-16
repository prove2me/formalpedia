-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_touch_iota1_lt_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_touch_iota1_lt_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:01:53.381197+00:00
-- url     : https://prove2.me/theorems/3ab3238d-ca8b-4d07-b455-1038581c12d4
-- title:
--   Wires touched by blk1 lie in the iota1 fibre below NL (QHNetRec)
-- statement:
--   Every global wire touched by the stage-one block \(\mathrm{blk1}\) lies in a single \(\iota_1\) fibre with local index strictly below \(NL=31359\), on the total-decoder network `QHNetRec`.
--
--   Fix a channel \(ch\) and a bit index \(b<1771\). If a wire \(w\) is touched by a gate support or an edge of \(\mathrm{blk1}(ch,b)\), then there exists a local index \(\ell\) such that
--
--   $$
--   \ell < NL \qquad\text{and}\qquad w = \iota_1(b)(\ell).
--   $$
--
--   This is the same touch certificate as `net0O2_blk1_touch_iota1_lt`, restated against `QHNetRec`. It follows from the corresponding \(\mathrm{chunkProg}\) statement by unfolding \(\mathrm{blk1}\), and is the parent of the prefix-label and \(\mathrm{LabGates}\) densify.
--
--   **Formalization Note.** The statement is identical to `net0O2_blk1_touch_iota1_lt`, with preamble importing `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec` rather than `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`. Solutions may import the QHNetRec theorem `net0O2_chunkProg_cs1_touch_iota1_lt_rec`; they must not import the parent QHNet module.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: blk1 touch fibre, restated on the total-decoder fork IntMul_Kappa_R8_Data_BitOppbankQHNetRec (d127abea).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (Instr)
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NL)
theorem net0O2_blk1_touch_iota1_lt_rec {ch : Ch} {b : ℕ} (hb : b < 1771)
    (w : Wr)
    (hw : ∃ instr ∈ blk1 ch b,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ∃ ℓ < NL, w = ι1 b ℓ := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
