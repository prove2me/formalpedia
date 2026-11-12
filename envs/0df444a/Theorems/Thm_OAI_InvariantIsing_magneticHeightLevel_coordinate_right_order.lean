-- Prove2me | Theorems.Thm_OAI_InvariantIsing_magneticHeightLevel_coordinate_right_order
-- name    : OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:39:41.493842+00:00
-- url     : https://prove2.me/theorems/355e9193-36e1-41bd-b781-8ba0ad53adc7
-- title:
--   OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticOffDiagonalHessian.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticOffDiagonalHessian.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   lemma magneticHeightLevel_coordinate_right_order (h : FieldStep) {s : ℝ}
--       (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
--       (hrs : r ∈ fieldStrictHeightCone h.depth)
--       (i j : Fin (h.depth + 1)) (hij : i < j) :
--       ∀ᶠ t in 𝓝[>] (0 : ℝ),
--         magneticHeightLevel h s (r + t • Pi.single j (1 : ℝ)) i ≤
--           magneticHeightLevel h s r i
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.fieldStrictHeightCone` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.magneticHeightLevel` (definitions bundle `OAIQ258005` of this split); `OAI.InvariantIsing.FieldStep` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticOffDiagonalHessian.lean (declaration OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order)

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma magneticHeightLevel_coordinate_right_order (h : FieldStep) {s : ℝ}
    (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hrs : r ∈ fieldStrictHeightCone h.depth)
    (i j : Fin (h.depth + 1)) (hij : i < j) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      magneticHeightLevel h s (r + t • Pi.single j (1 : ℝ)) i ≤
        magneticHeightLevel h s r i := by
  sorry

end InvariantIsing

end

end OAI
end
