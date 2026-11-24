-- Prove2me | Theorems.Thm_GlobalTheory_HCA_integral_mul_partial_eq_neg
-- name    : GlobalTheory.HCA.integral_mul_partial_eq_neg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:00:29.627608+00:00
-- url     : https://prove2.me/theorems/2a3c84ad-b4e9-4f0a-b15b-74bfbbf03b06
-- title:
--   HCA: integral mul partial eq neg
-- statement:
--   The HCA construction uses the integral mul partial eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L26-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L26-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
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
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.integral_mul_partial_eq_neg {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (j : Fin d)
    {u ψ : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ U) :
    ∫ x, u x * fderiv ℝ ψ x (ev j) = - ∫ x, fderiv ℝ u x (ev j) * ψ x := by sorry
