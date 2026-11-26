-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_scaled_queue_state_supremum_bounded_by_forcing
-- name    : ManyServerQED.Scheduling.scaled_queue_state_supremum_bounded_by_forcing
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:55:35.494147+00:00
-- url     : https://prove2.me/theorems/86cb039f-c057-5e89-ae84-17ad145f0c7d
-- title:
--   Polynomial pathwise growth of the scaled queue state
-- statement:
--   For a work-conserving controlled row, the supremum of the scaled state on a compact time interval is bounded by the supremum of the scaled forcing times the quadratic polynomial in the horizon coming from the service and abandonment rate bound.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_ManyServerQED_Scheduling_work_conserving_pathwise_growth
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.scaled_queue_state_supremum_bounded_by_forcing {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k) (n : ℕ) (hn : 0 < n) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsControlled n X0 X Ψ)
    (hWork : IsWorkConserving n X Ψ)
    (a : ℝ) (ha : 0 < a) (hμa : ∀ i, M.muN n i ≤ a) (hθa : ∀ i, M.thetaN n i ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    let W (ω : Ω) (t : ℝ) (i : Fin k) :=
      M.Xhat0 n X0 i + M.Ahat n ω t i -
      M.Rhat n ω (queueTime X Ψ ω i t / n) i -
      M.Shat n ω (busyTime Ψ ω i t / n) i +
      ((M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n) * t
    supDist (M.Xhat n X ω) (fun _ => 0) T ≤
      ENNReal.ofReal ((k : ℝ) * (1 + a * T) ^ 2) * supDist (W ω) (fun _ => 0) T := by sorry
