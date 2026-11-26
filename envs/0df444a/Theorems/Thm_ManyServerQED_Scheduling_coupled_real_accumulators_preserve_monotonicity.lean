-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_coupled_real_accumulators_preserve_monotonicity
-- name    : ManyServerQED.Scheduling.coupled_real_accumulators_preserve_monotonicity
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:41:36.322904+00:00
-- url     : https://prove2.me/theorems/a185f931-0f53-4484-9172-ed366915111d
-- title:
--   Monotone coordinates remain monotone on the coupled limit
-- statement:
--   A continuous scalar observation of a joint queue path limit is nondecreasing if the corresponding original observations are eventually nondecreasing.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.coupled_real_accumulators_preserve_monotonicity {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (hs : Tendsto s atTop atTop)
    (v : (Fin (k+k+k+2) → ℝ) → ℝ) (hv : Continuous v)
    (h : ∀ᶠ n in atTop, ∀ ω, MonotoneOn (fun t => v (Z n ω t)) (Ici (0:ℝ))) :
    ∀ᵐ ω ∂d.Q, Monotone (fun t : ℝ≥0 => v (d.limit ω t)) := by sorry
