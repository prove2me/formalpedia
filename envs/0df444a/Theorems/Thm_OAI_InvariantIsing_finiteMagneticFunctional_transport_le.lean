-- Prove2me | Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_transport_le
-- name    : OAI.InvariantIsing.finiteMagneticFunctional_transport_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:46.704065+00:00
-- url     : https://prove2.me/theorems/9eefb1ff-658a-40b6-a01a-c35c9fb49398
-- title:
--   OAI.InvariantIsing.finiteMagneticFunctional_transport_le: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.finiteMagneticFunctional_transport_le` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem finiteMagneticFunctional_transport_le {A B ι : Type*}
--       [Fintype A] [Fintype B] [Fintype ι]
--       (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
--       (w : A → B → ℝ) (γ b : A → ℝ) (δ c : B → ℝ)
--       (hw : ∀ a j, 0 ≤ w a j) (hγ : ∀ a, 0 ≤ γ a) (hδ : ∀ j, 0 < δ j)
--       (hγsum : ∑ a, γ a=1) (hδsum : ∑ j, δ j=1)
--       (hrow : ∀ a, ∑ j, w a j=γ a) (hcol : ∀ j, ∑ a, w a j=δ j) :
--       (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal ≤
--         (finiteMagneticFunctional (finiteR ρ eig hρ hsum) δ c).toReal+
--           ∑ a, ∑ j, w a j* |b a-c j|
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.finiteMagneticFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.finite_type_field_pressure_tendsto`, `OAI.InvariantIsing.physical_mean_wasserstein_field_pressure_tendsto` and `OAI.InvariantIsing.random_field_pressure_tendsto_ae` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticVariationalTransport.lean (declaration OAI.InvariantIsing.finiteMagneticFunctional_transport_le)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
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
import Definitions.Def_OAIQ258001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace InvariantIsing

theorem finiteMagneticFunctional_transport_le {A B ι : Type*}
    [Fintype A] [Fintype B] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (w : A → B → ℝ) (γ b : A → ℝ) (δ c : B → ℝ)
    (hw : ∀ a j, 0 ≤ w a j) (hγ : ∀ a, 0 ≤ γ a) (hδ : ∀ j, 0 < δ j)
    (hγsum : ∑ a, γ a=1) (hδsum : ∑ j, δ j=1)
    (hrow : ∀ a, ∑ j, w a j=γ a) (hcol : ∀ j, ∑ a, w a j=δ j) :
    (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) δ c).toReal+
        ∑ a, ∑ j, w a j* |b a-c j| := by
  sorry

end InvariantIsing

end

end OAI
end
