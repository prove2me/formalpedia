-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_cadlag_composition_with_continuous_nondecreasing_clock
-- name    : ManyServerQED.Scheduling.cadlag_composition_with_continuous_nondecreasing_clock
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:34:13.624981+00:00
-- url     : https://prove2.me/theorems/bfc9e7ba-a954-544c-9046-1c5802eddf4f
-- title:
--   Càdlàg paths under continuous nondecreasing clocks
-- statement:
--   Composing a real càdlàg path with a continuous nonnegative nondecreasing clock preserves its càdlàg property.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
open Filter Topology Set MeasureTheory
open BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.cadlag_composition_with_continuous_nondecreasing_clock (f c : ℝ → ℝ) (hf : IsCadlag f)
    (hc : ContinuousOn c (Ici (0:ℝ))) (hm : MonotoneOn c (Ici (0:ℝ)))
    (hn : ∀ t, 0 ≤ t → 0 ≤ c t) :
    IsCadlag (f ∘ c) := by sorry
