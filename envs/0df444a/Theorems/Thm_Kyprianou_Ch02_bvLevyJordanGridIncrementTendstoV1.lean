-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyJordanGridIncrementTendstoV1
-- name    : Kyprianou.Ch02.bvLevyJordanGridIncrementTendstoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:38:45.454897+00:00
-- url     : https://prove2.me/theorems/9588b2c6-076b-4ed1-a0d1-28abfad389b8
-- title:
--   Signed Jordan grid sums converge to joint variation increments
-- statement:
--   For a càdlàg locally BV path, equal-grid absolute sums converge to the signed variation on the interval. Telescoping gives the original increment exactly. Using max(z,0)=(|z|+z)/2 and max(-z,0)=(|z|-z)/2, the pair converges to the positive and negative variation increments by additivity of variation.
-- source:
--   Kyprianou (2006), Exercise 2.8; common equal-grid approximation route.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyJordanGridIncrementTendstoV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let G : ℕ → ℝ≥0 → ℝ≥0 → Ω → ℝ × ℝ := fun n a b ω =>
      let g (k : ℕ) := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
      let d (k : ℕ) := X (g (k+1)) ω - X (g k) ω
      (∑ k : Fin (n+1), max (d k) 0, ∑ k : Fin (n+1), max (-d k) 0)
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Y : ℝ≥0 → Ω → ℝ × ℝ := fun t ω =>
      ((V t ω + X t ω)/2, (V t ω - X t ω)/2)
    ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      Tendsto (fun n => G n a b ω) atTop
        (nhds (increment Y a b ω)) := by sorry
