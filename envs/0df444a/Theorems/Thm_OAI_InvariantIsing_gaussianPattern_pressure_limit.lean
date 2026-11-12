-- Prove2me | Theorems.Thm_OAI_InvariantIsing_gaussianPattern_pressure_limit
-- name    : OAI.InvariantIsing.gaussianPattern_pressure_limit
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:27:14.948508+00:00
-- url     : https://prove2.me/theorems/47c82c34-b205-4b23-81c0-2634a97ac1d6
-- title:
--   OAI.InvariantIsing.gaussianPattern_pressure_limit: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.gaussianPattern_pressure_limit` of [lean/OAI/Probability/InvariantIsing/Gaussian/GaussianPatternPressureLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Gaussian/GaussianPatternPressureLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem gaussianPattern_pressure_limit
--       (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       (hpub : PanchenkoTalagrandFieldPairInput)
--       (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
--       (hds : DavidsonSzarekInput.{u} α hα)
--       {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
--       (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
--       (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
--       (c : ℝ) :
--       TendstoInMeasure P (fun k ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)) atTop
--         (fun _ => gaussianPatternLimit α c) ∧
--       Tendsto (fun k => eLpNorm (fun ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)-
--         gaussianPatternLimit α c) 1 P) atTop (𝓝 0) ∧
--       Tendsto (fun k => ∫ ω, gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω) ∂P) atTop
--         (𝓝 (gaussianPatternLimit α c))
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.DavidsonSzarekInput` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput`, `OAI.InvariantIsing.MarchenkoPasturInput` and `OAI.InvariantIsing.PanchenkoTalagrandFieldPairInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.gaussianPatternCount`, `OAI.InvariantIsing.gaussianPatternLimit` and `OAI.InvariantIsing.gaussianPatternPressure` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.gaussianPattern_ground_limit` and `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Gaussian/GaussianPatternPressureLimit.lean (declaration OAI.InvariantIsing.gaussianPattern_pressure_limit)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Order.Lattice
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
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
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
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
universe u
namespace InvariantIsing

theorem gaussianPattern_pressure_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
    (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (c : ℝ) :
    TendstoInMeasure P (fun k ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)) atTop
      (fun _ => gaussianPatternLimit α c) ∧
    Tendsto (fun k => eLpNorm (fun ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)-
      gaussianPatternLimit α c) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω) ∂P) atTop
      (𝓝 (gaussianPatternLimit α c)) := by
  sorry

end InvariantIsing

end

end OAI
end
