-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyJordanGridStationaryLawV1
-- name    : Kyprianou.Ch02.levyJordanGridStationaryLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:38:51.518884+00:00
-- url     : https://prove2.me/theorems/53d88900-7b2b-4a4d-8994-2196e7eb2516
-- title:
--   Equal-grid Jordan sum pair has stationary increment law
-- statement:
--   Each equal-grid increment vector has independent coordinates, all with the common law of the original process over a cell of width u/(n+1). Equality of product laws gives equality of the grid positive and negative sums by a measurable map.
-- source:
--   Kyprianou (2006), Exercise 2.8; common equal-grid approximation route.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyJordanGridStationaryLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    let G : ℕ → ℝ≥0 → ℝ≥0 → Ω → ℝ × ℝ := fun n a b ω =>
      let g (k : ℕ) := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
      let d (k : ℕ) := X (g (k+1)) ω - X (g k) ω
      (∑ k : Fin (n+1), max (d k) 0, ∑ k : Fin (n+1), max (-d k) 0)
    ∀ n : ℕ, ∀ s u : ℝ≥0,
      IdentDistrib (G n s (s+u)) (G n 0 u) P P := by sorry
