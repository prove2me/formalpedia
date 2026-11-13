-- Prove2me | Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_ne_top_bot
-- name    : OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:10:19.190507+00:00
-- url     : https://prove2.me/theorems/8b1fc3f9-af96-4dd3-b806-484fa6ccfa08
-- title:
--   OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma finiteMagneticFunctional_ne_top_bot {A : Type*} [Fintype A]
--       (R : ℝ → ℝ) (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
--       (hRtop : variationalFunctional R ≠ ⊤) (hRbot : variationalFunctional R ≠ ⊥) :
--       finiteMagneticFunctional R γ c ≠ ⊤ ∧ finiteMagneticFunctional R γ c ≠ ⊥
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.finiteMagneticFunctional` and `OAI.InvariantIsing.variationalFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.compact_spectral_field_pressure_tendsto_of_mem`, `OAI.InvariantIsing.finiteMagneticFunctional_real_profile`, `OAI.InvariantIsing.finiteMagneticFunctional_transport_le`, `OAI.InvariantIsing.finite_physical_field_pressure_upper`, `OAI.InvariantIsing.finite_type_field_pressure_tendsto`, `OAI.InvariantIsing.physical_mean_wasserstein_field_pressure_tendsto` and `OAI.InvariantIsing.random_field_pressure_tendsto_ae` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalContinuity.lean (declaration OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot)

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
open scoped BigOperators

namespace InvariantIsing

lemma finiteMagneticFunctional_ne_top_bot {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hRtop : variationalFunctional R ≠ ⊤) (hRbot : variationalFunctional R ≠ ⊥) :
    finiteMagneticFunctional R γ c ≠ ⊤ ∧ finiteMagneticFunctional R γ c ≠ ⊥ := by
  sorry

end InvariantIsing

end

end OAI
end
