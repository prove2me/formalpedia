-- Prove2me | Theorems.Thm_GlobalTheory_HCA_integral_mul_dw_eq_neg_pow
-- name    : GlobalTheory.HCA.integral_mul_dw_eq_neg_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:59:33.782568+00:00
-- url     : https://prove2.me/theorems/1d2722c6-d94e-4842-8eec-bb98089e041a
-- title:
--   HCA: integral mul dw eq neg pow
-- statement:
--   The HCA construction uses the integral mul dw eq neg pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L126-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L126-L136

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

theorem GlobalTheory.HCA.integral_mul_dw_eq_neg_pow : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d))
    (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by sorry
