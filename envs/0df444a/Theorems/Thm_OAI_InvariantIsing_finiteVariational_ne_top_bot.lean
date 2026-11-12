-- Prove2me | Theorems.Thm_OAI_InvariantIsing_finiteVariational_ne_top_bot
-- name    : OAI.InvariantIsing.finiteVariational_ne_top_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:23.676209+00:00
-- url     : https://prove2.me/theorems/31f50acc-f7fa-4cb3-9075-864e2cedca28
-- title:
--   OAI.InvariantIsing.finiteVariational_ne_top_bot: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.finiteVariational_ne_top_bot` of [lean/OAI/Probability/InvariantIsing/Core/FiniteVariationalBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Core/FiniteVariationalBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory Set`, `open scoped BigOperators`):
--
--   ```lean
--   theorem finiteVariational_ne_top_bot {ι : Type*} [Fintype ι]
--       (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) :
--       variationalFunctional (finiteR ρ eig hρ hρsum) ≠ ⊤ ∧
--         variationalFunctional (finiteR ρ eig hρ hρsum) ≠ ⊥
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.variationalFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.CompactSpectralPartition.pressure_tendsto`, `OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto`, `OAI.InvariantIsing.cavity_window_minimum_variational_lower`, `OAI.InvariantIsing.finiteMagneticFunctional_real_profile`, `OAI.InvariantIsing.finiteMagneticFunctional_transport_le`, `OAI.InvariantIsing.finiteSpectrum_meanPressure_variational_upper`, `OAI.InvariantIsing.finite_physical_field_pressure_upper` and `OAI.InvariantIsing.finite_type_field_pressure_tendsto` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Core/FiniteVariationalBounds.lean (declaration OAI.InvariantIsing.finiteVariational_ne_top_bot)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

theorem finiteVariational_ne_top_bot {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) :
    variationalFunctional (finiteR ρ eig hρ hρsum) ≠ ⊤ ∧
      variationalFunctional (finiteR ρ eig hρ hρsum) ≠ ⊥ := by
  sorry

end InvariantIsing

end

end OAI
end
