-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_brownian_weighted_finite_observation_law
-- name    : ManyServerQED.Scheduling.brownian_weighted_finite_observation_law
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:32:11.393903+00:00
-- url     : https://prove2.me/theorems/c18aeb11-3f03-4fc1-a393-9930c78c5b07
-- title:
--   The law of weighted Brownian observations
-- statement:
--   The joint law of finitely many weighted observations of a standard Brownian motion depends only on the deterministic times and weights, including repeated times.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.brownian_weighted_finite_observation_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P')
    {m : ℕ} (t : Fin m → ℝ≥0) (c : Fin m → ℝ) :
    IdentDistrib (fun ω i => c i * B (t i) ω) (fun ω i => c i * C (t i) ω) P P' := by sorry
