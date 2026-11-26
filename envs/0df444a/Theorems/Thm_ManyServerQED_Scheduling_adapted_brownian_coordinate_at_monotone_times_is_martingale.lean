-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_adapted_brownian_coordinate_at_monotone_times_is_martingale
-- name    : ManyServerQED.Scheduling.adapted_brownian_coordinate_at_monotone_times_is_martingale
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:13:24.058027+00:00
-- url     : https://prove2.me/theorems/530424ca-7d7d-5ebc-940f-18db7ca816c9
-- title:
--   Sampling a filtered Brownian coordinate gives a martingale
-- statement:
--   For a Brownian motion adapted to a filtration and with its future increments independent of that filtration, each coordinate sampled at deterministic nondecreasing times is a discrete-time martingale for the sampled filtration.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Diffusion
open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.adapted_brownian_coordinate_at_monotone_times_is_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {k : ℕ} (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin k → ℝ) (hW : IsStdFBrownian P F W)
    {a : ℕ → ℝ≥0} (ha : Monotone a) (i : Fin k) :
    let H : Filtration ℕ mΩ := ⟨fun j => F (a j), fun _ _ h => F.mono (ha h), fun j => F.le (a j)⟩
    Martingale (fun j ω => W (a j) ω i) H P := by sorry
