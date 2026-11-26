-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_arrival_finite_observation_limit
-- name    : ManyServerQED.Scheduling.queue_arrival_finite_observation_limit
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:43:02.453593+00:00
-- url     : https://prove2.me/theorems/10e11207-d084-45ee-bec3-e0758c79ce1b
-- title:
--   Finite-dimensional Brownian limit for centered arrivals
-- statement:
--   For an arrival class in the many-server queue, finite vectors of observations of the centered scaled arrival process converge to those of a standard Brownian motion multiplied by the square root of the product of the limiting arrival rate and interarrival variance.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
import Theorems.Thm_DurrettProbability_donsker
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_DurrettProbability_Donsker
open Set Filter Topology MeasureTheory ProbabilityTheory DurrettProbability
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Topology Finset
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy DurrettProbability
open Filter Topology MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

theorem ManyServerQED.Scheduling.queue_arrival_finite_observation_limit {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) (i : Fin k)
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
    letI := M.isProb
    TendstoInDistribution (fun n ω j => M.Ahat n ω (τ j) i) atTop
      (fun ω j => Real.sqrt (M.lam i * M.cU2 i)*B (τ j).toNNReal ω) (fun _ => M.P) P' := by sorry
