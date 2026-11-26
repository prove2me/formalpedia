-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_state_growth_on_path_coupling
-- name    : ManyServerQED.Scheduling.queue_hjb_state_growth_on_path_coupling
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:41:14.898047+00:00
-- url     : https://prove2.me/theorems/a38463f2-a13c-57a2-b3ba-97a97dbf8be5
-- title:
--   Polynomial forcing bound for the coupled queue limit
-- statement:
--   The limiting queue state is bounded on each compact interval by a quadratic polynomial in the horizon times the sum of the initial, linear forcing and Brownian-coordinate suprema terms.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_scaled_queue_state_supremum_bounded_by_forcing
import Theorems.Thm_ManyServerQED_Scheduling_measurable_compact_supremum_of_evaluation_path
import Theorems.Thm_ManyServerQED_Scheduling_coupled_lipschitz_observable_compact_suprema_converge
open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_state_growth_on_path_coupling {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ) (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M L γ u0 f X Ψ) s)
    (hCadLaw : ∀ᶠ n in atTop, ∀ ω i, IsCadlag (fun t => queueHJBObservation M L γ u0 f X Ψ n ω t i)) :
    ∃ a : ℝ, 0 < a ∧ ∀ T : ℝ≥0, ∀ᵐ ω ∂d.Q, ∀ t ≤ T,
      ENNReal.ofReal (l1norm (d.state t ω)) ≤
        ENNReal.ofReal ((k:ℝ)*(1+a*(T:ℝ))^2) *
          (ENNReal.ofReal ((k:ℝ)*a*(1+(T:ℝ))) +
            ∑ i, ENNReal.ofReal (M.diffData.r i) *
              (⨆ u : Iic T, ENNReal.ofReal |d.noise u.1 ω i|)) := by sorry
