-- Prove2me | Theorems.Thm_GlobalTheory_T_false_of_sum_sq_eq_12_of_fourier_vanish_order_63
-- name    : GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:39:41.657383+00:00
-- url     : https://prove2.me/theorems/f9a888f2-ea7a-4d45-ba32-eaeb3d7d575a
-- title:
--   T: false of sum sq eq 12 of fourier vanish order 63
-- statement:
--   The T construction uses the false of sum sq eq 12 of fourier vanish order 63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormTwelveOrderSixtythreeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormTwelveOrderSixtythreeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythree
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythreeStatement
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

theorem GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 → ∑ k ∈ Finset.range 63, c k ^ 2 = 12 → (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j → ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by sorry
