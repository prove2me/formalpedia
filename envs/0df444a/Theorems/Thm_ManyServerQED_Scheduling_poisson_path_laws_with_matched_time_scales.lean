-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_poisson_path_laws_with_matched_time_scales
-- name    : ManyServerQED.Scheduling.poisson_path_laws_with_matched_time_scales
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:28:31.011433+00:00
-- url     : https://prove2.me/theorems/c527e5d7-abee-4ef1-8c50-a51c30bbacff
-- title:
--   Equality of time-scaled Poisson path laws at equal effective rates
-- statement:
--   Take two Poisson processes, possibly on different probability spaces. Sample each on its own nonnegative linear time scale. If their rates multiplied by those time scales agree, the sampled paths have the same law.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
import Definitions.Def_ManyServerQED_Scheduling_Model
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.poisson_path_laws_with_matched_time_scales {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (N : Ω → ℝ → ℝ) (N' : Ω' → ℝ → ℝ) (a b c d : ℝ)
    (hN : IsPoissonProcess P N a) (hN' : IsPoissonProcess P' N' b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hMatch : a * c = b * d) :
    IdentDistrib (fun ω (t : ℝ≥0) => N ω (c*t)) (fun ω (t : ℝ≥0) => N' ω (d*t)) P P' := by sorry
