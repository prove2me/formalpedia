-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_norm_eval_le
-- name    : GlobalTheory.MvPoly.norm_eval_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:24.704802+00:00
-- url     : https://prove2.me/theorems/3a6f0217-2ecf-5533-b5f4-f081825331bf
-- title:
--   Mv Poly: norm eval le
-- statement:
--   The Mv Poly construction uses the norm eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L264-L266

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

theorem GlobalTheory.MvPoly.norm_eval_le [NormOneClass K] [Fintype σ] (x : σ → K) (P : MvPolynomial σ K) :
    ‖eval x P‖ ≤ l1Norm P * max 1 ‖x‖ ^ P.totalDegree := by sorry
