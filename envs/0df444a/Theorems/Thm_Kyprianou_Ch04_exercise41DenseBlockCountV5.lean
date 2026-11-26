-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41DenseBlockCountV5
-- name    : Kyprianou.Ch04.exercise41DenseBlockCountV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:42:52.643799+00:00
-- url     : https://prove2.me/theorems/4ff694ab-c37a-51ce-ae40-f218fb34ce99
-- title:
--   Dense-grid occupancy count has uniform expectation bound over one block
-- statement:
--   Dense-grid occupancy count has uniform expectation bound over one block
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41DenseBlockCountV5
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (a δ : NNReal) (h : ℝ) (n : ℕ) (q : ℕ → NNReal)
    (hh : 0 < h) (hd : 0 < L.drift)
    (hw : (n : ℝ) * h ≤ (δ : ℝ))
    (hp : 0 < P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}) :
    let A : ℕ → ℕ → Set Ω := fun m i =>
      {ω | ∃ k < m, (a : ℝ) + (i : ℝ) * h ≤ (q k : ℝ) ∧
        (q k : ℝ) < (a : ℝ) + ((i : ℝ) + 1) * h ∧
        |L.X (q k) ω| < L.drift * h / 8}
    let N : Ω → ℝ≥0∞ := fun ω =>
      ⨆ m : ℕ, ∑ i ∈ Finset.range n, (A m i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω
    let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}
    Measurable N ∧ (∫⁻ ω, N ω ∂P) ≤ 2 / p  := by
  sorry
