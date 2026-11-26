-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteBlockGridV4
-- name    : Kyprianou.Ch04.exercise41FiniteBlockGridV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:24:29.020142+00:00
-- url     : https://prove2.me/theorems/b4aa17cf-a638-4b16-9a4e-cce708630cc7
-- title:
--   Finite grids within one slope window satisfy the occupancy bound without an explicit difference grid
-- statement:
--   Finite grids within one slope window satisfy the occupancy bound without an explicit difference grid
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteBlockGridV4
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (I : Finset ℕ) (D : ℕ → Finset NNReal) (a δ : NNReal) (h : ℝ)
    (hh : 0 < h) (hd : 0 < L.drift)
    (hBlock : ∀ i ∈ I, ∀ t ∈ D i, a ≤ t ∧ t < a + δ)
    (hcell : ∀ i ∈ I, ∀ t ∈ D i,
      (a : ℝ) + (i : ℝ) * h ≤ (t : ℝ) ∧
      (t : ℝ) < (a : ℝ) + ((i : ℝ) + 1) * h) :
    let A : ℕ → Set Ω := fun i =>
      {ω | ∃ t ∈ D i, |L.X t ω| < L.drift * h / 8}
    let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}
    (∀ i ∈ I, MeasurableSet (A i)) ∧ p * ∑ i ∈ I, P (A i) ≤ 2  := by
  sorry
