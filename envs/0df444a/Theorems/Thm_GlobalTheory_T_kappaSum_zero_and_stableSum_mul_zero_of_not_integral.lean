-- Prove2me | Theorems.Thm_GlobalTheory_T_kappaSum_zero_and_stableSum_mul_zero_of_not_integral
-- name    : GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:16.921511+00:00
-- url     : https://prove2.me/theorems/19ce2885-f90e-545d-99f0-4312890b06d5
-- title:
--   T: kappa Sum zero and stable Sum mul zero of not integral
-- statement:
--   The T construction uses the kappa Sum zero and stable Sum mul zero of not integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KappaSumZeroAndStableSumMulZeroOfNotIntegralStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KappaSumZeroAndStableSumMulZeroOfNotIntegralStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) → InvAlg.kapSum B₁ B₂ = 0 ∧ B₁.stSum * B₂.stSum = 0 := by sorry
