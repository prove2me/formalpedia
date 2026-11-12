-- Prove2me | Theorems.Thm_OAI_InvariantIsing_magneticEntropyFunctional_lower
-- name    : OAI.InvariantIsing.magneticEntropyFunctional_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:10:18.828435+00:00
-- url     : https://prove2.me/theorems/466fd30f-c3b2-452f-802f-0b3e985c3d46
-- title:
--   OAI.InvariantIsing.magneticEntropyFunctional_lower: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.magneticEntropyFunctional_lower` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory Set`, `open scoped BigOperators`):
--
--   ```lean
--   lemma magneticEntropyFunctional_lower {A : Type*} [Fintype A]
--       (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
--       (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) :
--       ((-Real.log 2 : ℝ) : EReal) ≤ magneticEntropyFunctional γ mag p
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.OverlapPath` and `OAI.InvariantIsing.magneticEntropyFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.finiteMagneticVariational_ne_top_bot`, `OAI.InvariantIsing.finite_physical_field_pressure_upper` and `OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalBounds.lean (declaration OAI.InvariantIsing.magneticEntropyFunctional_lower)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing

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

lemma magneticEntropyFunctional_lower {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) :
    ((-Real.log 2 : ℝ) : EReal) ≤ magneticEntropyFunctional γ mag p := by
  sorry

end InvariantIsing

end

end OAI
end
