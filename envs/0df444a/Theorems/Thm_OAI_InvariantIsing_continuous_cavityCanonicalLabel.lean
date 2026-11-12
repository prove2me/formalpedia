-- Prove2me | Theorems.Thm_OAI_InvariantIsing_continuous_cavityCanonicalLabel
-- name    : OAI.InvariantIsing.continuous_cavityCanonicalLabel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:44.33272+00:00
-- url     : https://prove2.me/theorems/032d04ba-95a9-4c14-a59f-c143e030c7e3
-- title:
--   OAI.InvariantIsing.continuous_cavityCanonicalLabel: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.continuous_cavityCanonicalLabel` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityCanonicalLabels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityCanonicalLabels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   lemma continuous_cavityCanonicalLabel {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
--       (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) :
--       Continuous (cavityCanonicalLabel ρ eig hρ hρsum p a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityCanonicalLabel` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.OverlapPath` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_canonical_group_block_tendsto`, `OAI.InvariantIsing.cavity_finite_cascade_block_average`, `OAI.InvariantIsing.cavity_finite_model_numerator`, `OAI.InvariantIsing.cavity_haar_gibbs_numerator_match`, `OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match`, `OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match` and `OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityCanonicalLabels.lean (declaration OAI.InvariantIsing.continuous_cavityCanonicalLabel)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma continuous_cavityCanonicalLabel {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) :
    Continuous (cavityCanonicalLabel ρ eig hρ hρsum p a) := by
  sorry

end InvariantIsing

end

end OAI
end
