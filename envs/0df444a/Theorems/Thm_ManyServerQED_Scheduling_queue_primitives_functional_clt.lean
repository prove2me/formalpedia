-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_primitives_functional_clt
-- name    : ManyServerQED.Scheduling.queue_primitives_functional_clt
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:16:54.604524+00:00
-- url     : https://prove2.me/theorems/06fb3c06-4e44-5774-b977-bd492f0d177a
-- title:
--   Joint Brownian limit for the queue primitives
-- statement:
--   For the independent arrival, service and abandonment primitives of a many-server system sequence, the centered diffusion-scaled vector \((\widehat A^n,\widehat S^n,\widehat R^n)\) has a joint functional central limit. Its coordinates are independent centered Brownian motions with variance rates \(\lambda_i C_{U,i}^2\), \(\mu_i\), and \(\theta_i\), respectively. The weak convergence is expressed by a coupling in which the paths converge uniformly on compact time intervals almost surely. Coordinates with zero limiting variance are identically zero in the limit.
-- source:
--   Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, Lemma 4(i), https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_primitives_functional_clt {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B : Fin (k + k + k) → ℝ≥0 → Ω' → ℝ),
      IsProbabilityMeasure P' ∧ (∀ j, IsBrownianReal (B j) P') ∧
      iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P' ∧
      CouplingConverges M.P P'
        (fun n ω t => Fin.append (Fin.append (M.Ahat n ω t) (M.Shat n ω t)) (M.Rhat n ω t))
        (fun ω t j => Fin.append (Fin.append (fun i => Real.sqrt (M.lam i * M.cU2 i))
            (fun i => Real.sqrt (M.mu i))) (fun i => Real.sqrt (M.theta i)) j *
          B j t.toNNReal ω) := by sorry
