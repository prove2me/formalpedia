-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_det_le
-- name    : GlobalTheory.MvPoly.l1Norm_det_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:48.852372+00:00
-- url     : https://prove2.me/theorems/e6fab9f3-bff5-4447-9463-02e2e0f78ada
-- title:
--   Mv Poly: l1 Norm det le
-- statement:
--   The Mv Poly construction uses the l1 Norm det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L183-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L183-L195

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

theorem GlobalTheory.MvPoly.l1Norm_det_le [NormOneClass K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) {R : ℝ} (h : ∀ a b, l1Norm (M a b) ≤ R) :
    l1Norm M.det ≤ (Fintype.card ι).factorial * R ^ Fintype.card ι := by sorry
