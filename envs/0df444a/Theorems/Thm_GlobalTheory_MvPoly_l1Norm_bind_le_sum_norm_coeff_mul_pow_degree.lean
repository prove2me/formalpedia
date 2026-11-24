-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_bind_le_sum_norm_coeff_mul_pow_degree
-- name    : GlobalTheory.MvPoly.l1Norm_bind_le_sum_norm_coeff_mul_pow_degree
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:43.18255+00:00
-- url     : https://prove2.me/theorems/4dd5da70-4aa0-42c6-b096-ac241971f1e0
-- title:
--   Mv Poly: l1 Norm bind le sum norm coeff mul pow degree
-- statement:
--   The Mv Poly construction uses the l1 Norm bind le sum norm coeff mul pow degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L218-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L218-L226

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

theorem GlobalTheory.MvPoly.l1Norm_bind_le_sum_norm_coeff_mul_pow_degree [NormOneClass K] (f : σ → MvPolynomial τ K) (P : MvPolynomial σ K)
    {R : ℝ} (h : ∀ i, l1Norm (f i) ≤ R) :
    l1Norm (bind₁ f P) ≤ ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree := by sorry
