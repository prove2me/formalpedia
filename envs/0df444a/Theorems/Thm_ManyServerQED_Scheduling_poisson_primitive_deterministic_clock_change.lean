-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_poisson_primitive_deterministic_clock_change
-- name    : ManyServerQED.Scheduling.poisson_primitive_deterministic_clock_change
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:32:22.955686+00:00
-- url     : https://prove2.me/theorems/c8e40c32-2251-4fb2-8041-647588583f3f
-- title:
--   Deterministic rescaling of a Poisson clock
-- statement:
--   If a counting process is a Poisson process of rate $a$, then running it at a constant positive speed $c$ gives a Poisson process of rate $ac$.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Model
open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.poisson_primitive_deterministic_clock_change {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → ℝ → ℝ} {a : ℝ} (hN : IsPoissonProcess P N a) (c : ℝ) (hc : 0 < c) :
    IsPoissonProcess P (fun ω t => N ω (c*t)) (a*c) := by sorry
