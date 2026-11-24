-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalPastCylinderPiSystemV1
-- name    : Kyprianou.Ch03.canonicalPastCylinderPiSystemV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:16:54.199372+00:00
-- url     : https://prove2.me/theorems/d8902ded-fc49-4806-b96f-bab4c45e5c31
-- title:
--   Finite-coordinate cylinders of the canonical past form a pi system
-- statement:
--   Intersect two cylinders by combining their finite index sets and pulling back both measurable finite-dimensional events to the common finite coordinate vector.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; auxiliary reductions of canonicalProductZeroOriginMarginalsV1 and canonicalPastMeasuresEqOfFiniteMarginalsV1.

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalPastCylinderPiSystemV1
    (t : NNReal) :
    IsPiSystem {A : Set {path : NNReal → ℝ // path 0 = 0} | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
      (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = (fun w => I.restrict w.val) ⁻¹' E} := by
  sorry
