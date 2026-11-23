-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_degree_le_totalDegree
-- name    : GlobalTheory.MvPoly.degree_le_totalDegree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:58.914363+00:00
-- url     : https://prove2.me/theorems/d63b4dbe-5f7e-4324-9c0d-19027fbb9c3e
-- title:
--   Mv Poly: degree le total Degree
-- statement:
--   The Mv Poly construction uses the degree le total Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L215-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L215-L216

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

theorem GlobalTheory.MvPoly.degree_le_totalDegree {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {α : σ →₀ ℕ}
    (h : α ∈ P.support) : α.degree ≤ P.totalDegree := by sorry
