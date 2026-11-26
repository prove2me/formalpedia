-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_primitives_joint_finite_observation_limit
-- name    : ManyServerQED.Scheduling.queue_primitives_joint_finite_observation_limit
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:56:01.876928+00:00
-- url     : https://prove2.me/theorems/3450d6d5-f7cd-5290-b1f1-d237f86f9b33
-- title:
--   Joint finite-dimensional limits for all queue primitives
-- statement:
--   For the many-server queue sequence, the joint finite-dimensional laws of the centered scaled arrival, service, and abandonment primitives converge to those of independent scaled Brownian motions. The factors are respectively the square roots of the arrival rate times its interarrival variance, the service rate, and the abandonment rate.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_poisson_primitive_deterministic_clock_change
import Theorems.Thm_ManyServerQED_Scheduling_poisson_rows_centered_finite_observation_limit
import Theorems.Thm_ManyServerQED_Scheduling_joint_weak_limit_of_independent_finite_family
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
open Set MeasureTheory ProbabilityTheory

theorem ManyServerQED.Scheduling.queue_primitives_joint_finite_observation_limit {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k)
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    (B : Fin (k+k+k) → ℝ≥0 → Ω' → ℝ)
    (hB : ∀ j, IsBrownianReal (B j) P')
    (hBc : ∀ j ω, Continuous (fun t => B j t ω))
    (hiB : iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P')
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
    letI := M.isProb
    TendstoInDistribution
      (fun n ω j => Fin.append (Fin.append (M.Ahat n ω (τ j)) (M.Shat n ω (τ j))) (M.Rhat n ω (τ j)))
      atTop (fun ω j i =>
        Fin.append (Fin.append (fun l => Real.sqrt (M.lam l*M.cU2 l))
          (fun l => Real.sqrt (M.mu l))) (fun l => Real.sqrt (M.theta l)) i *
        B i (τ j).toNNReal ω) (fun _ => M.P) P' := by sorry
