-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_filtered_brownian_coordinate_finite_sample_maximal_bound
-- name    : ManyServerQED.Scheduling.filtered_brownian_coordinate_finite_sample_maximal_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:50:41.448596+00:00
-- url     : https://prove2.me/theorems/d70952bd-4bb7-4009-9ebf-accd69af0d38
-- title:
--   Doob bounds for finite Brownian samples
-- statement:
--   For finitely many deterministic sample times no later than a fixed horizon, the Lp norm of the maximum absolute value of a filtered Brownian coordinate is bounded by the Doob factor p divided by p minus one times the Lp norm of the terminal coordinate, for p greater than one.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
import Theorems.Thm_AvramDividend_Classical_avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
import Theorems.Thm_ManyServerQED_Scheduling_adapted_brownian_coordinate_at_monotone_times_is_martingale
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.filtered_brownian_coordinate_finite_sample_maximal_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → Fin k → ℝ)
    (hW : IsStdFBrownian P F W) (i : Fin k)
    (T : ℝ≥0) (J : Finset ℝ≥0) (hJ : J.Nonempty) (hJT : ∀ t ∈ J, t ≤ T)
    (p : ℝ) (hp : 1 < p) :
    eLpNorm (fun ω => J.sup' hJ (fun t => ‖W t ω i‖)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p/(p-1))*eLpNorm (fun ω => W T ω i) (ENNReal.ofReal p) P := by sorry
