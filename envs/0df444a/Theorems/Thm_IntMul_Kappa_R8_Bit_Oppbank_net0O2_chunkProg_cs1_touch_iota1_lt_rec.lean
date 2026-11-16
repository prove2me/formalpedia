-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_chunkProg_cs1_touch_iota1_lt_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_chunkProg_cs1_touch_iota1_lt_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:01:36.496031+00:00
-- url     : https://prove2.me/theorems/e5e94c31-3029-43f9-8513-ba99c398c3fa
-- title:
--   Wires touched by chunkProg on cs1 lie in the iota1 fibre below NL (QHNetRec)
-- statement:
--   Every global wire touched by the stage-one chunk program on \(\mathrm{cs1}\) lies in a single \(\iota_1\) fibre with local index strictly below \(NL=31359\), on the total-decoder network `QHNetRec`.
--
--   Fix a channel \(ch\) and a bit index \(b<1771\). If a wire \(w\) is touched by a gate support or an edge of \(\mathrm{chunkProg}(\iota_1(b), ch.e_1(b), \mathrm{cs1})\), then there exists a local index \(\ell\) such that
--
--   $$
--   \ell < NL \qquad\text{and}\qquad w = \iota_1(b)(\ell).
--   $$
--
--   This is the same touch certificate as `net0O2_chunkProg_cs1_touch_iota1_lt`, restated against `QHNetRec`. It uses the \(\mathrm{cs1}\) local-wire bound as its data hypothesis and is the parent of the \(\mathrm{blk1}\) touch densify.
--
--   **Formalization Note.** The statement is identical to `net0O2_chunkProg_cs1_touch_iota1_lt`, with preamble importing `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec` rather than `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`. Solutions may import the QHNetRec theorem `net0O2_cs1_locals_lt_NL_rec`; they must not import the parent QHNet module.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: chunkProg cs1 touch fibre, restated on the total-decoder fork IntMul_Kappa_R8_Data_BitOppbankQHNetRec (d127abea).

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
theorem net0O2_chunkProg_cs1_touch_iota1_lt_rec {ch : Ch} {b : ℕ} (hb : b < 1771)
    (w : Wr)
    (hw : ∃ instr ∈ chunkProg (ι1 b) (ch.e1 b) cs1,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ∃ ℓ < NL, w = ι1 b ℓ := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
