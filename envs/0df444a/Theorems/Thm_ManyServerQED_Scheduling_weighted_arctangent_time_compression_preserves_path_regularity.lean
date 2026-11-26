-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_weighted_arctangent_time_compression_preserves_path_regularity
-- name    : ManyServerQED.Scheduling.weighted_arctangent_time_compression_preserves_path_regularity
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:55:50.88698+00:00
-- url     : https://prove2.me/theorems/8fc40124-dfdd-47e2-a041-70b173e3cce3
-- title:
--   Path regularity under weighted arctangent time compression
-- statement:
--   Compress the nonnegative time axis into the unit interval by the inverse of the map sending t to t divided by one plus t. Apply arctangent coordinatewise and multiply by one minus the compressed time. The map carries càdlàg paths to càdlàg unit paths and continuous paths to continuous unit paths.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_Reiman84_QueueLength_Paths
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy Reiman84.QueueLength

theorem ManyServerQED.Scheduling.weighted_arctangent_time_compression_preserves_path_regularity {k : ℕ} (f : ℝ → Fin k → ℝ) :
    let z (s : ℝ) := max 0 (1-s) • (fun i => Real.arctan (f (s/(1-s)) i))
    ((∀ i, IsCadlag (fun t => f t i)) → IsCadlag01 z) ∧
    (ContinuousOn f (Set.Ici 0) → ContinuousOn z (Set.Icc (0:ℝ) 1)) := by sorry
