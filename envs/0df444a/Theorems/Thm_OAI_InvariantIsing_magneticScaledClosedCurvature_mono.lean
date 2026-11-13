-- Prove2me | Theorems.Thm_OAI_InvariantIsing_magneticScaledClosedCurvature_mono
-- name    : OAI.InvariantIsing.magneticScaledClosedCurvature_mono
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:40:00.057982+00:00
-- url     : https://prove2.me/theorems/a99ae7b4-26b1-4ba6-a2ec-40abc5641e76
-- title:
--   OAI.InvariantIsing.magneticScaledClosedCurvature_mono: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.magneticScaledClosedCurvature_mono` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticScaledCurvatureOrder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticScaledCurvatureOrder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open Filter Set`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem magneticScaledClosedCurvature_mono (L : List (ℝ × ℝ≥0))
--       (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
--       {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
--       {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
--       magneticScaledClosedCurvature L hL α ζ (v, s) ≤
--         magneticScaledClosedCurvature L hL β ζ (v, s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.magneticScaledClosedCurvature` (definitions bundle `OAIQ258005` of this split).
--
--   **Used by.** The proof of `OAI.InvariantIsing.magneticFieldLevel_radial` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticScaledCurvatureOrder.lean (declaration OAI.InvariantIsing.magneticScaledClosedCurvature_mono)

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ258005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticScaledClosedCurvature_mono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledClosedCurvature L hL α ζ (v, s) ≤
      magneticScaledClosedCurvature L hL β ζ (v, s) := by
  sorry

end InvariantIsing

end

end OAI
end
