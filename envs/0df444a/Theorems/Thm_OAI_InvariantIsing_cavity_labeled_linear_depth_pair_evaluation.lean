-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_labeled_linear_depth_pair_evaluation
-- name    : OAI.InvariantIsing.cavity_labeled_linear_depth_pair_evaluation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:22:10.641841+00:00
-- url     : https://prove2.me/theorems/332531e0-df81-4981-b74e-65e08bc582d8
-- title:
--   OAI.InvariantIsing.cavity_labeled_linear_depth_pair_evaluation: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_labeled_linear_depth_pair_evaluation` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityLinearDepthEvaluation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityLinearDepthEvaluation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped Matrix NNReal`):
--
--   ```lean
--   theorem cavity_labeled_linear_depth_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
--       {d k : ℕ} (hk : 0 < k) (h : FieldStep)
--       (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
--       (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
--       (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
--       (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
--       (hres : L.transpose * R * L = (v : ℝ) • 1)
--       (c : ℝ) (s : EuclideanSpace ℝ (Fin d)) (ψ : ℕ → ℝ)
--       {C : ℝ} (hψ : ∀ i, |ψ i| ≤ C) :
--       cavityLabeledLinearDepthPairMean h S R L c s ψ =
--         ∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.fieldLevelIndex` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.PanchenkoTalagrandFieldPairInput`, `OAI.InvariantIsing.cavityLabeledLinearDepthPairMean` and `OAI.InvariantIsing.fieldStepVariance` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.FieldStep` and `OAI.InvariantIsing.pathMeasure` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_linear_rooted_depth_evaluation` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityLinearDepthEvaluation.lean (declaration OAI.InvariantIsing.cavity_labeled_linear_depth_pair_evaluation)

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

theorem cavity_labeled_linear_depth_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
    {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (c : ℝ) (s : EuclideanSpace ℝ (Fin d)) (ψ : ℕ → ℝ)
    {C : ℝ} (hψ : ∀ i, |ψ i| ≤ C) :
    cavityLabeledLinearDepthPairMean h S R L c s ψ =
      ∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure := by
  sorry

end InvariantIsing

end

end OAI
end
