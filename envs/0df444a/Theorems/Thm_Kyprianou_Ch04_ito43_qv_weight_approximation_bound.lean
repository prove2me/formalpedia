-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_weight_approximation_bound
-- name    : Kyprianou.Ch04.ito43_qv_weight_approximation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:42:08.550906+00:00
-- url     : https://prove2.me/theorems/bff9972f-d7be-5636-a755-9df20bdcf0f9
-- title:
--   Finite weighted energy perturbation bound
-- statement:
--   A uniform error in weights is bounded by the tolerance times the sum of nonnegative cell energies; apply the finite triangle inequality and pointwise comparison.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_weight_approximation_bound {ι : Type} (S : Finset ι) (g h e : ι → ℝ) (δ : ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) (hh : ∀ i ∈ S, |g i-h i| ≤ δ) :
    |∑ i ∈ S, (g i-h i)*e i| ≤ δ * ∑ i ∈ S, e i := by sorry
