-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_gap_identity_on_coupled_limit
-- name    : ManyServerQED.Scheduling.queue_hjb_gap_identity_on_coupled_limit
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:50:22.950299+00:00
-- url     : https://prove2.me/theorems/bf3845c1-4daf-5ebe-8faf-72b55426d7ba
-- title:
--   The HJB gap identity survives the joint path coupling
-- statement:
--   With a measurable density for the limiting accumulated drift and the transferred local Lipschitz estimates on the coupled rows, the limiting HJB gap equals limiting running cost plus the discounted drift against the HJB gradient minus the discounted Hamiltonian integral.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_rows_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
import Theorems.Thm_ManyServerQED_Scheduling_right_endpoint_stieltjes_sums_for_cadlag_weight
import Theorems.Thm_ManyServerQED_Scheduling_stieltjes_integrals_stable_under_uniform_weight_and_primitive_limits
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_gap_identity_on_coupled_limit {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (hC : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s)
    (a : ℝ) (ha : 0 < a) (b : d.Ω' → ℝ → Fin k → ℝ)
    (hBm : Measurable (fun z : d.Ω' × ℝ => b z.1 z.2))
    (hB : ∀ ω t, ‖b ω t‖ ≤ a*(1+l1norm (d.state t.toNNReal ω)))
    (hPrim : ∀ᵐ ω ∂d.Q, ∀ T : ℝ≥0,
      (∫ s in (0:ℝ)..(T:ℝ), b ω s) = d.driftIntegral T ω-d.driftIntegral 0 ω)
    (hRows : ∀ᵐ ω ∂d.Q, ∀ᶠ n in atTop, ∀ s t C, 0 ≤ s → s ≤ t →
      (∀ u ∈ Icc s t, a*(1+∑ i : Fin k,
        |d.row n ω u (Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i)))|) ≤ C) →
      ‖(fun i : Fin k => d.row n ω t (Fin.castAdd 2 (Fin.natAdd (k+k) i))) -
        (fun i : Fin k => d.row n ω s (Fin.castAdd 2 (Fin.natAdd (k+k) i)))‖ ≤ C*(t-s)) :
    ∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0, d.gap t ω = d.runningCost t ω +
        ∫ r in (0:ℝ)..(t:ℝ), Real.exp (-γ*r) *
          ((∑ i, b ω r i * grad f (d.state r.toNNReal ω) i) -
            hamiltonian M.diffData (costOfTilde Lt) (d.state r.toNNReal ω)
              (grad f (d.state r.toNNReal ω))) := by sorry
