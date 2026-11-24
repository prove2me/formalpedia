-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_sum_norm_coeff_mul_pow_of_isHomogeneous
-- name    : GlobalTheory.MvPoly.sum_norm_coeff_mul_pow_of_isHomogeneous
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:30:09.298724+00:00
-- url     : https://prove2.me/theorems/1769a8a5-19e7-4d55-acae-d92692b23a4e
-- title:
--   Mv Poly: sum norm coeff mul pow of is Homogeneous
-- statement:
--   The Mv Poly construction uses the sum norm coeff mul pow of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L236-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L236-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K]

theorem GlobalTheory.MvPoly.sum_norm_coeff_mul_pow_of_isHomogeneous {P : MvPolynomial σ K} {d : ℕ}
    (hP : P.IsHomogeneous d) (R : ℝ) :
    ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree = l1Norm P * R ^ d := by sorry
