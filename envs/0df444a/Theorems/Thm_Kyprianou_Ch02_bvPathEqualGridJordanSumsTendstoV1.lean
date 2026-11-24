-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvPathEqualGridJordanSumsTendstoV1
-- name    : Kyprianou.Ch02.bvPathEqualGridJordanSumsTendstoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:48:49.192792+00:00
-- url     : https://prove2.me/theorems/52508524-0e62-4bd3-87ba-1e7030b893c5
-- title:
--   Equal-grid positive and negative increments converge to deterministic Jordan increments
-- statement:
--   Use convergence of absolute increment sums and telescoping signed increments; express each positive and negative part as half the sum or difference of absolute and signed increments.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvPathEqualGridJordanSumsTendstoV1
    (f : ℝ≥0 → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn f univ)
    (hr : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t) :
    let g (n k : ℕ) : ℝ≥0 := a+(b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    let d (n k : ℕ) : ℝ := f (g n (k+1)) - f (g n k)
    let v := variationOnFromTo f univ
    Tendsto (fun n => (∑ k : Fin (n+1), max (d n k) 0,
      ∑ k : Fin (n+1), max (-d n k) 0)) atTop
      (nhds (((v a b + (f b-f a))/2), ((v a b-(f b-f a))/2))) := by sorry
