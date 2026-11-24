-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyJordanGridPairAEMeasurableV1
-- name    : Kyprianou.Ch02.levyJordanGridPairAEMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:38:50.263747+00:00
-- url     : https://prove2.me/theorems/9eba6c7f-b62a-41de-8345-284d0818cb0e
-- title:
--   Equal-grid Jordan sum pair is almost everywhere measurable
-- statement:
--   The original coordinates are almost everywhere measurable; finite sums of positive and negative parts of their differences are almost everywhere measurable.
-- source:
--   Kyprianou (2006), Exercise 2.8; common equal-grid approximation route.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyJordanGridPairAEMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    let G : ℕ → ℝ≥0 → ℝ≥0 → Ω → ℝ × ℝ := fun n a b ω =>
      let g (k : ℕ) := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
      let d (k : ℕ) := X (g (k+1)) ω - X (g k) ω
      (∑ k : Fin (n+1), max (d k) 0, ∑ k : Fin (n+1), max (-d k) 0)
    ∀ n : ℕ, ∀ a b : ℝ≥0, AEMeasurable (G n a b) P := by sorry
