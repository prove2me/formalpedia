-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_finrank_restrictTotalDegree
-- name    : GlobalTheory.MvPoly.finrank_restrictTotalDegree
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:09.683202+00:00
-- url     : https://prove2.me/theorems/fd6c81cf-76a4-4693-846d-f2cad4e0b944
-- title:
--   Mv Poly: finrank restrict Total Degree
-- statement:
--   The Mv Poly construction uses the finrank restrict Total Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L316-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L316-L319

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

theorem GlobalTheory.MvPoly.finrank_restrictTotalDegree (R : Type*) [CommRing R] [Nontrivial R] (d : ℕ) :
    Module.finrank R (restrictTotalDegree σ R d) = (Fintype.card σ + d).choose d := by sorry
