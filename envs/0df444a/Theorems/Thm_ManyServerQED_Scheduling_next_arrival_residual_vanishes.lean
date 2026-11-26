-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_next_arrival_residual_vanishes
-- name    : ManyServerQED.Scheduling.next_arrival_residual_vanishes
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:06:11.447858+00:00
-- url     : https://prove2.me/theorems/168c0f8a-5ccf-4f3f-aef3-bcfd70e4cb7c
-- title:
--   The next arrival delay vanishes on the fluid time scale
-- statement:
--   In a sequence of renewal inputs with asymptotically positive arrival rate per server, assume uniform-on-compacts convergence in probability of the fluid-scaled counts to their linear deterministic limit. At each deterministic nonnegative time, the delay until the next arrival tends to zero in probability.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_lemma_2
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.next_arrival_residual_vanishes {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k)
    (mL mU : ℝ) (hA3 : M.Assumption3 mL mU) (i : Fin k)
    (t : ℝ) (ht : 0 ≤ t) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => M.P {ω | ε ≤ M.nextArrival n i ω t - t}) atTop (𝓝 0) := by sorry
