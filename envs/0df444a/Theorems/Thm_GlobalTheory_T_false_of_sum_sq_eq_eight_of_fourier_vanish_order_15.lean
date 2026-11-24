-- Prove2me | Theorems.Thm_GlobalTheory_T_false_of_sum_sq_eq_eight_of_fourier_vanish_order_15
-- name    : GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:39:44.628368+00:00
-- url     : https://prove2.me/theorems/06a98d8f-15fb-4838-b74a-d5476fdc8de0
-- title:
--   T: false of sum sq eq eight of fourier vanish order 15
-- statement:
--   The T construction uses the false of sum sq eq eight of fourier vanish order 15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormEightOfFourierVanishingOrderFifteenStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormEightOfFourierVanishingOrderFifteenStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormEightOfFourierVanishingOrderFifteen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormEightOfFourierVanishingOrderFifteenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 → (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by sorry
