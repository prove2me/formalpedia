-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_ncard_setOf_degree_le
-- name    : GlobalTheory.MvPoly.ncard_setOf_degree_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:29:16.301793+00:00
-- url     : https://prove2.me/theorems/2db0df8a-4eec-4956-86d6-95688ec2d671
-- title:
--   Mv Poly: ncard set Of degree le
-- statement:
--   The Mv Poly construction uses the ncard set Of degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L306-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L306-L312

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
variable [Fintype σ] [DecidableEq σ]
omit [DecidableEq σ]

theorem GlobalTheory.MvPoly.ncard_setOf_degree_le (d : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ d}.ncard = (Fintype.card σ + d).choose d := by sorry
