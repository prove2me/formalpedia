-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_support_subset_monomialsLE
-- name    : GlobalTheory.MvPoly.support_subset_monomialsLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:10.962128+00:00
-- url     : https://prove2.me/theorems/fe28805a-8c7e-43c3-9cc6-d61869e8e51a
-- title:
--   Mv Poly: support subset monomials LE
-- statement:
--   The Mv Poly construction uses the support subset monomials LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L292-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L292-L295

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

theorem GlobalTheory.MvPoly.support_subset_monomialsLE {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ} :
    P.support ⊆ monomialsLE σ d ↔ P.totalDegree ≤ d := by sorry
