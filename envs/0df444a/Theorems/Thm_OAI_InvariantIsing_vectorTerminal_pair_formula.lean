-- Prove2me | Theorems.Thm_OAI_InvariantIsing_vectorTerminal_pair_formula
-- name    : OAI.InvariantIsing.vectorTerminal_pair_formula
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:32:24.844179+00:00
-- url     : https://prove2.me/theorems/e2232ec8-b277-49e7-b827-78954db9be6d
-- title:
--   OAI.InvariantIsing.vectorTerminal_pair_formula: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.vectorTerminal_pair_formula` of [lean/OAI/Probability/InvariantIsing/Fields/VectorPairIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/VectorPairIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped NNReal`):
--
--   ```lean
--   theorem vectorTerminal_pair_formula {N : ℕ} (hN : 0 < N) (n : ℕ)
--       (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
--       (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ)
--       (he : ∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
--         Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
--           (labeledLeafLaw n p.1))
--       (Φ : ℕ × (Fin n → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hΦ : Measurable Φ)
--       {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
--       vectorTerminalPairMean N n b v F z Φ =
--         ∫ α : ℕ → LabeledLeaf n,
--           markPairPathMean n (vectorTerminalAncestorKernel N n b v F hF)
--             (labeledCommonDepth n (α 0) (α 1)) z z
--             (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w)) ∂cascadeReplicaLaw n b
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.VectorTerminalCoordinates` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.markPairPathMean` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.vectorTerminalAncestorKernel`, `OAI.InvariantIsing.vectorTerminalCoordinateLaw` and `OAI.InvariantIsing.vectorTerminalPairMean` (definitions bundle `OAIQ258004` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.HasLinearGrowth`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.cascadeReplicaLaw`, `OAI.IsingPerceptron.labeledCommonDepth`, `OAI.IsingPerceptron.labeledEnergy`, `OAI.IsingPerceptron.labeledLeafLaw`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace` and `OAI.IsingPerceptron.markForestOfCoords` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.panchenkoTalagrandFieldPair_proved` and `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/VectorPairIntegral.lean (declaration OAI.InvariantIsing.vectorTerminal_pair_formula)

import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Definitions.Def_OAIQ258004

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vectorTerminal_pair_formula {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ)
    (he : ∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
      Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
        (labeledLeafLaw n p.1))
    (Φ : ℕ × (Fin n → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hΦ : Measurable Φ)
    {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
    vectorTerminalPairMean N n b v F z Φ =
      ∫ α : ℕ → LabeledLeaf n,
        markPairPathMean n (vectorTerminalAncestorKernel N n b v F hF)
          (labeledCommonDepth n (α 0) (α 1)) z z
          (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w)) ∂cascadeReplicaLaw n b := by
  sorry

end InvariantIsing

end

end OAI
end
