-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_continuous_functional_iterPartialDeriv
-- name    : GlobalTheory.T.exists_continuous_functional_iterPartialDeriv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:36.999795+00:00
-- url     : https://prove2.me/theorems/f998b08e-85bf-45e1-acaf-8e01bb24ce0f
-- title:
--   T: exists continuous functional iter Partial Deriv
-- statement:
--   The T construction uses the exists continuous functional iter Partial Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsContinuousFunctionalIterPartialDerivStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsContinuousFunctionalIterPartialDerivStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDerivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_continuous_functional_iterPartialDeriv : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (R : B →ₗ[ℂ] (E d → ℂ)), (∀ x ∈ U, Continuous fun u => R u x) → (∀ u, ContDiffOn ℝ ∞ (R u) U) → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : B →L[ℂ] ℂ, ∀ u, l u = dw w (R u) x := by sorry
