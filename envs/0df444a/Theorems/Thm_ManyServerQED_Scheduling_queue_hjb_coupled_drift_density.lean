-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_coupled_drift_density
-- name    : ManyServerQED.Scheduling.queue_hjb_coupled_drift_density
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:46:45.051461+00:00
-- url     : https://prove2.me/theorems/ad066ec0-48e2-5751-8223-3b0aa5059889
-- title:
--   Measurable drift density of the limiting queue observation
-- statement:
--   On a joint queue path coupling, the accumulated limiting drift admits a measurable density with linear growth in the limiting state. The corresponding weighted interval Lipschitz bounds hold almost surely on the coupled rows eventually.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_rows_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_coupling_transfers_weighted_path_lipschitz_bounds
import Theorems.Thm_ManyServerQED_Scheduling_weighted_lipschitz_path_has_measurable_drift_density
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_coupled_drift_density {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (hC : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s) :
    let m := k+k+k+2
    let A (z : Fin m → ℝ) (i : Fin k) := z (Fin.castAdd 2 (Fin.natAdd (k+k) i))
    let R (z : Fin m → ℝ) := 1+∑ i : Fin k, |z (Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i)))|
    ∃ a > (0:ℝ), ∃ b : d.Ω' → ℝ → Fin k → ℝ,
      Measurable (fun z : d.Ω' × ℝ => b z.1 z.2) ∧
      (∀ ω t, ‖b ω t‖ ≤ a*R (d.limit ω (t.toNNReal:ℝ))) ∧
      (∀ᵐ ω ∂d.Q, ∀ T : ℝ≥0, (∫ s in (0:ℝ)..(T:ℝ), b ω s) =
        d.driftIntegral T ω-d.driftIntegral 0 ω) ∧
      ∀ᵐ ω ∂d.Q, ∀ᶠ n in atTop, ∀ s t C, 0 ≤ s → s ≤ t →
        (∀ u ∈ Icc s t, a*R (d.row n ω u) ≤ C) →
        ‖A (d.row n ω t)-A (d.row n ω s)‖ ≤ C*(t-s) := by sorry
