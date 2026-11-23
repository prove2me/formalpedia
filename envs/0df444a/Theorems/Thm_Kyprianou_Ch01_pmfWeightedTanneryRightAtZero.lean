-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfWeightedTanneryRightAtZero
-- name    : Kyprianou.Ch01.pmfWeightedTanneryRightAtZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:07:42.089285+00:00
-- url     : https://prove2.me/theorems/2afce52b-c7f8-406d-8ac0-5857c9ca3d75
-- title:
--   Probability-mass-function weighted Tannery convergence at zero without moment assumptions
-- statement:
--   Let p be any PMF on natural numbers, with no finite first moment assumption. For a real family f(t,k) tending to zero as t decreases to 0 for each fixed k, suppose |f(t,k)|≤1 uniformly for all k at sufficiently small positive t. Then the PMF weighted infinite sum of f(t,k) also tends to zero. Prove using the already available Mathlib tendsto_tsum_of_dominated_convergence and ENNReal.summable_toReal p.tsum_coe_ne_top. This is the analytic dominated-convergence device needed for the two-jump rarity bound after an unbounded offspring mark.
-- source:
--   Tannery's theorem for series, pinned Mathlib.Analysis.Normed.Group.Tannery and probability mass function normalisation; Kyprianou (2006) Chapter 1 reverse Lamperti generator.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.pmfWeightedTanneryRightAtZero
    (p : PMF ℕ) (f : ℝ → ℕ → ℝ)
    (hpoint : ∀ k : ℕ,
      Tendsto (fun t : ℝ => f t k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ k : ℕ, |f t k| ≤ 1) :
    Tendsto
      (fun t : ℝ => ∑' k : ℕ, (p k).toReal * f t k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  sorry
