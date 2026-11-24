-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalPastCylinderGenerateV1
-- name    : Kyprianou.Ch03.canonicalPastCylinderGenerateV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:17:00.676421+00:00
-- url     : https://prove2.me/theorems/f8937d87-e152-430c-aceb-f04d1deaa72c
-- title:
--   Finite-coordinate cylinders generate the raw canonical past sigma algebra
-- statement:
--   Each single coordinate event is a cylinder with a singleton time set. Conversely, the finite coordinate vector is measurable in the raw past by coordinatewise measurability.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; auxiliary reductions of canonicalProductZeroOriginMarginalsV1 and canonicalPastMeasuresEqOfFiniteMarginalsV1.

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalPastCylinderGenerateV1
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (t : NNReal) :
    PerfCorrMSQ.natFiltr X t = MeasurableSpace.generateFrom
      {A : Set {path : NNReal → ℝ // path 0 = 0} | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
      (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = (fun w => I.restrict w.val) ⁻¹' E} := by
  sorry
