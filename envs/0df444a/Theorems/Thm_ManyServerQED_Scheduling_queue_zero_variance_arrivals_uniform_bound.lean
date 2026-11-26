-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_zero_variance_arrivals_uniform_bound
-- name    : ManyServerQED.Scheduling.queue_zero_variance_arrivals_uniform_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:22:47.53016+00:00
-- url     : https://prove2.me/theorems/c52f8655-4ac5-46a3-acaa-89e7a565e966
-- title:
--   Uniform bound for deterministic interarrival times
-- statement:
--   For a queue arrival class with zero interarrival variance, its scaled centered arrival process has absolute value at most the reciprocal of the square root of n, on a single full-probability event for every n and every nonnegative time.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Model
open Filter Topology MeasureTheory ProbabilityTheory Set Finset
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped NNReal ENNReal

theorem ManyServerQED.Scheduling.queue_zero_variance_arrivals_uniform_bound {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) (hi : M.cU2 i = 0) :
    ∀ᵐ ω ∂M.P, ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      |M.Ahat n ω t i| ≤ 1/Real.sqrt n := by sorry
