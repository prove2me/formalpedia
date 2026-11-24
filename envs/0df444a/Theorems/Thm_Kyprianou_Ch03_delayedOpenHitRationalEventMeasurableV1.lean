-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedOpenHitRationalEventMeasurableV1
-- name    : Kyprianou.Ch03.delayedOpenHitRationalEventMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:29:15.007799+00:00
-- url     : https://prove2.me/theorems/48413a71-aef0-42c6-9b57-e56c365ca97f
-- title:
--   Rational witness event for a delayed open hit is measurable
-- statement:
--   Every rational witness event depends on a time earlier than s and is therefore measurable in the completed natural filtration at s; take the countable union.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed open hitting.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedOpenHitRationalEventMeasurableV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (a s : NNReal) (B : Set ℝ) (hB : IsOpen B) :
    MeasurableSet[F s] (⋃ q : ℚ, ⋃ (_ : a ≤ Real.toNNReal q ∧ Real.toNNReal q < s),
      {w | X (Real.toNNReal q) w ∈ B}) := by
  sorry
