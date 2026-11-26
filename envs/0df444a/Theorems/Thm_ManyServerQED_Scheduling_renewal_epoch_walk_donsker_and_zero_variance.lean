-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_renewal_epoch_walk_donsker_and_zero_variance
-- name    : ManyServerQED.Scheduling.renewal_epoch_walk_donsker_and_zero_variance
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:57:57.986265+00:00
-- url     : https://prove2.me/theorems/06a9d4b2-e46f-48f4-912f-1a99c831cab1
-- title:
--   Donsker convergence of the renewal epoch interpolation
-- statement:
--   For one queue class with positive interarrival variance, the polygonal sum of the centered normalized interarrival variables converges in distribution on the unit interval to standard Brownian motion. If the variance is zero, every normalized interarrival variable equals its common mean one almost surely, simultaneously over all interarrival indices.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_DurrettProbability_donsker
import Definitions.Def_ManyServerQED_Scheduling_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy DurrettProbability
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.renewal_epoch_walk_donsker_and_zero_variance {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) (i : Fin k)
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    letI : IsProbabilityMeasure M.P := M.isProb
    (0 < M.cU2 i →
      TendstoInDistribution (fun n : ℕ =>
        walkPath (fun j ω => (M.U i (j+1) ω-1)/Real.sqrt (M.cU2 i)) n)
        atTop (brownianPath B) (fun _ => M.P) P') ∧
    (M.cU2 i = 0 → ∀ᵐ ω ∂M.P, ∀ j : ℕ, M.U i (j+1) ω = 1) := by sorry
