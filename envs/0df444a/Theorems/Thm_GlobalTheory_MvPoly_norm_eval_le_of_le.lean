-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_norm_eval_le_of_le
-- name    : GlobalTheory.MvPoly.norm_eval_le_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:29:37.600285+00:00
-- url     : https://prove2.me/theorems/5e3ee563-87a7-4117-9511-27e098befcbf
-- title:
--   Mv Poly: norm eval le of le
-- statement:
--   The Mv Poly construction uses the norm eval le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L257-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L257-L262

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

theorem GlobalTheory.MvPoly.norm_eval_le_of_le [NormOneClass K] (x : σ → K) (P : MvPolynomial σ K) {R : ℝ}
    (h : ∀ i, ‖x i‖ ≤ R) {d : ℕ} (hd : P.totalDegree ≤ d) :
    ‖eval x P‖ ≤ l1Norm P * max 1 R ^ d := by sorry
