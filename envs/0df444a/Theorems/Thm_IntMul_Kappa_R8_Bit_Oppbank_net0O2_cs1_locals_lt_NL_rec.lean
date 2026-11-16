-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_cs1_locals_lt_NL_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_cs1_locals_lt_NL_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:01:36.873407+00:00
-- url     : https://prove2.me/theorems/bf0f4a6f-f7fb-49f1-8822-3174c5be2365
-- title:
--   Local endpoints of the stage-one chunk list cs1 lie strictly below NL (QHNetRec)
-- statement:
--   Every local wire index that appears as a move or XOR endpoint in the stage-one chunk list \(\mathrm{cs1}\) on the total-decoder network `QHNetRec` is strictly below \(NL=31359\).
--
--   Formally, if \(\ell\) occurs as a move source or as an XOR endpoint in some chunk of \(\mathrm{cs1}\), then
--
--   $$
--   \ell < NL.
--   $$
--
--   This is the same bound as `net0O2_cs1_locals_lt_NL`, restated against `QHNetRec`. It is the composition of \(\mathrm{genF}\) local-preservation with the \(W_{1F}\) wire bound, and is the data hypothesis of the \(\mathrm{chunkProg}\) / \(\mathrm{blk1}\) touch densify.
--
--   **Formalization Note.** The statement is identical to `net0O2_cs1_locals_lt_NL`, with preamble importing `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec` rather than `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`. Solutions may import the QHNetRec theorems `net0O2_genF_locals_of_W_rec` and `net0O2_W1F_wires_lt_NL_rec` only; they must not import the parent QHNet module.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: cs1 local-wire bound, restated on the total-decoder fork IntMul_Kappa_R8_Data_BitOppbankQHNetRec (d127abea).

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
theorem net0O2_cs1_locals_lt_NL_rec (ℓ : ℕ)
    (hℓ : ∃ ch ∈ cs1,
      (∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) :
    ℓ < NL := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
