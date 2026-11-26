-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_joint_queue_hjb_observation_asymptotic_interval_modulus
-- name    : ManyServerQED.Scheduling.joint_queue_hjb_observation_asymptotic_interval_modulus
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:42:18.577964+00:00
-- url     : https://prove2.me/theorems/4b8dc0a2-d5fc-410c-bfd4-3484b6708f5e
-- title:
--   Asymptotic modulus of the joint HJB queue observations
-- statement:
--   The state, normalized noise, accumulated drift, discounted cost and discounted HJB gap jointly have an asymptotically vanishing oscillation modulus on every compact interval under a work-conserving policy sequence.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_queue_effective_noise_asymptotic_interval_modulus
import Theorems.Thm_ManyServerQED_Scheduling_queue_diffusion_drift_remainder_uoc
import Theorems.Thm_ManyServerQED_Scheduling_controlled_compact_containment
import Theorems.Thm_ManyServerQED_Scheduling_finite_coordinate_modulus_controls_vector_modulus
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.joint_queue_hjb_observation_asymptotic_interval_modulus {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧
      M.IsAdmissible n (X n) (Ψ n) ∧ IsWorkConserving n (X n) (Ψ n))
    (f : (Fin k → ℝ) → ℝ) (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (T : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    let Z := queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ
    ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖Z n ω s-Z n ω t‖} ≤ ENNReal.ofReal η := by sorry
