-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_positive_variance_arrivals_uniform_walk_approximation
-- name    : ManyServerQED.Scheduling.queue_positive_variance_arrivals_uniform_walk_approximation
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:22:52.094075+00:00
-- url     : https://prove2.me/theorems/d315579b-c115-41d7-8cce-a65e7f76a7fb
-- title:
--   Uniform approximation of centered arrivals by the normalized epoch walk
-- statement:
--   For a positive-variance arrival stream of the queue, its centered scaled counting process on a fixed horizon is uniformly approximated in probability by the negative of the scaled interpolated epoch walk evaluated at the deterministic arrival-rate clock, with the interpolation index increased by a fixed integer factor.
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

theorem ManyServerQED.Scheduling.queue_positive_variance_arrivals_uniform_walk_approximation {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) (i : Fin k) (hVar : 0 < M.cU2 i)
    (P' : Measure Ω') [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    (T : ℝ) (hT : 0 ≤ T) (J : ℕ) (hJ : (M.lam i + 1)*T+3 ≤ J) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => M.P {ω | ∃ t ∈ Icc (0:ℝ) T, ε ≤
        |M.Ahat n ω t i + (Real.sqrt (M.cU2 i)*Real.sqrt (J:ℝ)) *
          walkPath (fun j ω => (M.U i (j+1) ω-1)/Real.sqrt (M.cU2 i)) (J*n) ω
          (projIcc 0 1 zero_le_one ((M.lamN n i/n)*t/(J:ℝ)))|}) atTop (𝓝 0) := by sorry
