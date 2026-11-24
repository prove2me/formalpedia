-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvRightContinuousEqualGridVariationTendstoV1
-- name    : Kyprianou.Ch02.bvRightContinuousEqualGridVariationTendstoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:33:23.131989+00:00
-- url     : https://prove2.me/theorems/9fb5fc0f-d800-4eab-ba2f-dff8f4ce91d6
-- title:
--   Absolute increment sums on equal grids converge to bounded variation
-- statement:
--   Use monotone right approximants and right continuity to converge in eVariationOn. The variation on each grid image equals its consecutive edistance sum. Convert to real using finite variation.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvRightContinuousEqualGridVariationTendstoV1
    (f : ℝ≥0 → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hBV : LocallyBoundedVariationOn f univ)
    (hr : ∀ t, ContinuousWithinAt f (Ici t) t) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), |f (g n (k+1)) - f (g n k)|)
      atTop (nhds (variationOnFromTo f univ a b)) := by sorry
