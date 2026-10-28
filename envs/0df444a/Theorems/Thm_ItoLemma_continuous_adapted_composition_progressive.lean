-- Prove2me | Theorems.Thm_ItoLemma_continuous_adapted_composition_progressive
-- name    : ItoLemma.continuous_adapted_composition_progressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:35:22.466984+00:00
-- url     : https://prove2.me/theorems/8a09a475-e52b-46eb-be8e-21f5a9009c1d
-- title:
--   Continuous Functionals of Continuous Adapted Processes Are Progressive
-- statement:
--   If Y is a continuous-path adapted process taking values in R² and φ is a continuous map from R² to R, then the scalar process φ(Y_t) is progressively measurable relative to the same filtration. This provides the progressive-measurability hypothesis for state-dependent coefficients used in the Itô formula and product rule.
-- source:
--   Reusable extraction of the accepted lemma S66.prog_comp in the full Itô chain-rule proof, accepted Prove2Me submission e4199398-3f38-4045-8e68-46254a555325. Uses the accepted progressivelyMeasurable_of_rightContinuous result.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists

open MeasureTheory ProbabilityTheory LevyStochCalc
open Filter Topology

universe u

theorem ItoLemma.continuous_adapted_composition_progressive
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {Y : ℝ → Ω → (Fin 2 → ℝ)}
    (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hYa : ∀ t, Measurable[ℱ t] (Y t))
    {φ : (Fin 2 → ℝ) → ℝ} (hφ : Continuous φ) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => φ (Y s ω)) := by sorry
