-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteGridOccupancyV3
-- name    : Kyprianou.Ch04.exercise41FiniteGridOccupancyV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:06:39.387556+00:00
-- url     : https://prove2.me/theorems/39846513-b6db-55c3-92af-76d5866f716b
-- title:
--   Uniform finite-grid occupancy estimate for positive-drift BV spectrally negative Levy paths
-- statement:
--   For every finite family of cell observation grids with a common bounded positive difference grid, the near-zero hit events are measurable and their probabilities have sum bounded by two divided by the positive-slope-window probability.
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteGridOccupancyV3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (I : Finset ℕ) (D : ℕ → Finset NNReal) (b : ℕ → NNReal)
    (R : Finset NNReal) (δ : NNReal) (a h : ℝ)
    (hh : 0 < h) (hd : 0 < L.drift)
    (hD : ∀ i ∈ I, ∀ t ∈ D i, t ≤ b i)
    (hcell : ∀ i ∈ I, ∀ t ∈ D i,
      a + (i : ℝ) * h ≤ (t : ℝ) ∧
      (t : ℝ) < a + ((i : ℝ) + 1) * h)
    (hR : ∀ u ∈ R, 0 < u ∧ u ≤ δ)
    (hDiff : ∀ i ∈ I, ∀ j ∈ I, i < j →
      ∀ s ∈ D i, ∀ t ∈ D j, t - s ∈ R) :
    let C : NNReal → Set Ω := fun t => {ω | |L.X t ω| < L.drift * h / 8}
    let A : ℕ → Set Ω := fun i => {ω | ∃ t ∈ D i, ω ∈ C t}
    let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}
    (∀ i ∈ I, MeasurableSet (A i)) ∧
      p * ∑ i ∈ I, P (A i) ≤ 2  := by
  sorry
