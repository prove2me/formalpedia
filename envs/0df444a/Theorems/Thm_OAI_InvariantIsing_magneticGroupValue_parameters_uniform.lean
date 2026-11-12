-- Prove2me | Theorems.Thm_OAI_InvariantIsing_magneticGroupValue_parameters_uniform
-- name    : OAI.InvariantIsing.magneticGroupValue_parameters_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:10:48.703694+00:00
-- url     : https://prove2.me/theorems/2cdd4f4d-1495-4dab-a6e0-74deb83086c1
-- title:
--   OAI.InvariantIsing.magneticGroupValue_parameters_uniform: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.magneticGroupValue_parameters_uniform` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticGroupParameterBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticGroupParameterBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   lemma magneticGroupValue_parameters_uniform {A : Type*} [Fintype A]
--       (γ s : ℕ → A → ℝ) (δ t : A → ℝ)
--       (hγ : Tendsto γ atTop (𝓝 δ)) (hs : Tendsto s atTop (𝓝 t))
--       {r : ℝ} (hr : r<1) (hst : ∀ a, |t a| ≤ r)
--       (hsk : ∀ᶠ k in atTop, ∀ a, |s k a| ≤ r) (H : ℝ) :
--       ∀ ε>0, ∀ᶠ k in atTop, ∀ h : FieldStep, h.height (Fin.last h.depth) ≤ H →
--         |magneticGroupValue (γ k) (s k) h-magneticGroupValue δ t h|<ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.FieldStep` and `OAI.InvariantIsing.magneticGroupValue` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.finite_physical_field_pressure_upper` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticGroupParameterBound.lean (declaration OAI.InvariantIsing.magneticGroupValue_parameters_uniform)

import Mathlib
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Definitions.Def_InvariantIsing

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma magneticGroupValue_parameters_uniform {A : Type*} [Fintype A]
    (γ s : ℕ → A → ℝ) (δ t : A → ℝ)
    (hγ : Tendsto γ atTop (𝓝 δ)) (hs : Tendsto s atTop (𝓝 t))
    {r : ℝ} (hr : r<1) (hst : ∀ a, |t a| ≤ r)
    (hsk : ∀ᶠ k in atTop, ∀ a, |s k a| ≤ r) (H : ℝ) :
    ∀ ε>0, ∀ᶠ k in atTop, ∀ h : FieldStep, h.height (Fin.last h.depth) ≤ H →
      |magneticGroupValue (γ k) (s k) h-magneticGroupValue δ t h|<ε := by
  sorry

end InvariantIsing

end

end OAI
end
