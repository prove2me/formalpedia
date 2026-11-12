-- Prove2me | Theorems.Thm_OAI_InvariantIsing_CompactSpectralPartition_selected_pressure_tendsto
-- name    : OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:18:55.652838+00:00
-- url     : https://prove2.me/theorems/e47521a0-20ef-45e6-89ba-889f38f7ceb0
-- title:
--   OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto` of [lean/OAI/Probability/InvariantIsing/Spectral/SelectedPartitionPressure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Spectral/SelectedPartitionPressure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing.CompactSpectralPartition`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology Classical Function`):
--
--   ```lean
--   lemma selected_pressure_tendsto {ν : ProbabilityMeasure ℝ} {a b δ : ℝ}
--       (P : CompactSpectralPartition ν a b δ)
--       (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       (hpub : PanchenkoTalagrandFieldPairInput)
--       (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
--       [∀ N, (μ N).IsMulRightInvariant]
--       (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
--       (eig : (k : ℕ) → Fin (D k) → ℝ)
--       (hweak : Tendsto (fun k => empiricalSpectralLaw (hD k) (eig k)) atTop (𝓝 ν)) :
--       Tendsto (fun k => ∫ V, rotatedPressure (fun i => P.lowerValue (eig k i))
--         (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
--         (𝓝 (variationalFunctional (measureR (P.law : Measure ℝ) P.edge)).toReal) ∧
--       Tendsto (fun k => ∫ V, rotatedPressure (fun i => P.upperValue (eig k i))
--         (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
--         (𝓝 (variationalFunctional (measureR (P.law : Measure ℝ) P.edge)).toReal)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace`, `OAI.InvariantIsing.CompactSpectralPartition`, `OAI.InvariantIsing.CompactSpectralPartition.edge`, `OAI.InvariantIsing.CompactSpectralPartition.law`, `OAI.InvariantIsing.CompactSpectralPartition.lowerValue` and `OAI.InvariantIsing.CompactSpectralPartition.upperValue` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput` and `OAI.InvariantIsing.PanchenkoTalagrandFieldPairInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.Orthogonal`, `OAI.InvariantIsing.empiricalSpectralLaw`, `OAI.InvariantIsing.matrixRotation`, `OAI.InvariantIsing.measureR`, `OAI.InvariantIsing.rotatedPressure` and `OAI.InvariantIsing.variationalFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.selected_spectral_pressure_tendsto` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Spectral/SelectedPartitionPressure.lean (declaration OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.Disjointed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Function
namespace InvariantIsing

namespace CompactSpectralPartition

lemma selected_pressure_tendsto {ν : ProbabilityMeasure ℝ} {a b δ : ℝ}
    (P : CompactSpectralPartition ν a b δ)
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (eig : (k : ℕ) → Fin (D k) → ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hD k) (eig k)) atTop (𝓝 ν)) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => P.lowerValue (eig k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR (P.law : Measure ℝ) P.edge)).toReal) ∧
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => P.upperValue (eig k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR (P.law : Measure ℝ) P.edge)).toReal) := by
  sorry

end CompactSpectralPartition
end InvariantIsing

end

end OAI
end
