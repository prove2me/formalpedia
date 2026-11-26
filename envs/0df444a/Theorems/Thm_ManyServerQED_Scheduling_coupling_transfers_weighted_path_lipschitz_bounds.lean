-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_coupling_transfers_weighted_path_lipschitz_bounds
-- name    : ManyServerQED.Scheduling.coupling_transfers_weighted_path_lipschitz_bounds
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:41:31.49158+00:00
-- url     : https://prove2.me/theorems/0b3d4cee-1a03-4931-8e65-3e0308ae9399
-- title:
--   Couplings preserve weighted Lipschitz estimates on path increments
-- statement:
--   Suppose a continuous observation of each original path has an increment bound by the length of that interval times the supremum of a nonnegative Lipschitz weight of the original path. Then the same bound holds almost surely for the coupled rows eventually and for their locally uniform limit.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_measurable_compact_supremum_of_evaluation_path
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.coupling_transfers_weighted_path_lipschitz_bounds {Ω E : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (hs : Tendsto s atTop atTop)
    (A : (Fin (k+k+k+2) → ℝ) → E) (hA : Continuous A)
    (R : (Fin (k+k+k+2) → ℝ) → ℝ) (hR : Continuous R) (hRn : ∀ z, 0 ≤ R z)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ x y, |R x-R y| ≤ L*∑ i, |x i-y i|)
    (hOrig : ∀ᶠ n in atTop, ∀ ω,
      (∀ t, 0 ≤ t → ContinuousWithinAt (Z n ω) (Ici t) t) ∧
      ∀ s t C, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, R (Z n ω u) ≤ C) →
        ‖A (Z n ω t)-A (Z n ω s)‖ ≤ C*(t-s)) :
    (∀ᵐ ω ∂d.Q, ∀ᶠ n in atTop, ∀ s t C, 0 ≤ s → s ≤ t →
      (∀ u ∈ Icc s t, R (d.row n ω u) ≤ C) →
        ‖A (d.row n ω t)-A (d.row n ω s)‖ ≤ C*(t-s)) ∧
    (∀ᵐ ω ∂d.Q, ∀ s t C, 0 ≤ s → s ≤ t →
      (∀ u ∈ Icc s t, R (d.limit ω u) ≤ C) →
        ‖A (d.limit ω t)-A (d.limit ω s)‖ ≤ C*(t-s)) := by sorry
