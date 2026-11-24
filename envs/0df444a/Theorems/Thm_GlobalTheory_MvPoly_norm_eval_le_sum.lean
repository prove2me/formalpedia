-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_norm_eval_le_sum
-- name    : GlobalTheory.MvPoly.norm_eval_le_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:59.89691+00:00
-- url     : https://prove2.me/theorems/d0034f99-43bb-4303-8dbd-65ad4dbc3f07
-- title:
--   Mv Poly: norm eval le sum
-- statement:
--   The Mv Poly construction uses the norm eval le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L248-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L248-L255

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

theorem GlobalTheory.MvPoly.norm_eval_le_sum [NormOneClass K] (x : σ → K) (P : MvPolynomial σ K) {R : ℝ}
    (h : ∀ i, ‖x i‖ ≤ R) : ‖eval x P‖ ≤ ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree := by sorry
