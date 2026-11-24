-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_sum_norm_coeff_mul_pow_le
-- name    : GlobalTheory.MvPoly.sum_norm_coeff_mul_pow_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:30:27.93288+00:00
-- url     : https://prove2.me/theorems/b6e8772c-11e8-4999-aaf0-02d8691e2cd1
-- title:
--   Mv Poly: sum norm coeff mul pow le
-- statement:
--   The Mv Poly construction uses the sum norm coeff mul pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L228-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L228-L234

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

theorem GlobalTheory.MvPoly.sum_norm_coeff_mul_pow_le (P : MvPolynomial σ K) {R : ℝ} (hR : 0 ≤ R) {d : ℕ}
    (hd : P.totalDegree ≤ d) :
    ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree ≤ l1Norm P * max 1 R ^ d := by sorry
