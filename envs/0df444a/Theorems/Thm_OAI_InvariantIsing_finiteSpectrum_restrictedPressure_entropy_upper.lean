-- Prove2me | Theorems.Thm_OAI_InvariantIsing_finiteSpectrum_restrictedPressure_entropy_upper
-- name    : OAI.InvariantIsing.finiteSpectrum_restrictedPressure_entropy_upper
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:26:45.488348+00:00
-- url     : https://prove2.me/theorems/c2ddc839-8724-4229-833d-7819284199b1
-- title:
--   OAI.InvariantIsing.finiteSpectrum_restrictedPressure_entropy_upper: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.finiteSpectrum_restrictedPressure_entropy_upper` of [lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedSpectrumEntropyUpper.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedSpectrumEntropyUpper.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem finiteSpectrum_restrictedPressure_entropy_upper
--       (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
--       (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
--       (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
--       (C : (k : ℕ) → Finset (Spin (N k))) (hC : ∀ k, (C k).Nonempty)
--       (eig : (k : ℕ) → Fin (N k) → ℝ)
--       (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
--       (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
--       (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
--       (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
--       (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
--       (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
--       (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
--       (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
--       (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
--       (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
--       (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
--       (d : ℝ) (hd : 0 < d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
--       (S : ℝ) (hS : ∀ H ε : ℝ, 0<ε → ∀ᶠ k in atTop,
--         ∀ (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i), (∑ i, a i) ≤ H →
--           constrainedBlockValue (C k) (contactFieldStep cut hc hfirst hlast a ha)+
--             fieldPairing trial (contactFieldStep cut hc hfirst hlast a ha)/2 ≤ S+ε) :
--       ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
--         (∫ U : SpecialOrthogonal (N k),
--           restrictedRotatedPressure (C k) (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
--         S + spectralFunctional (finiteR ρ lam hρpos hρsum) trial + ε
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.finiteR` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.contactFieldStep` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.HaarConcentrationInput` and `OAI.InvariantIsing.constrainedBlockValue` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.restrictedRotatedPressure` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Spin`, `OAI.InvariantIsing.fieldPairing`, `OAI.InvariantIsing.pathMeasure` and `OAI.InvariantIsing.spectralFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.finite_physical_field_pressure_upper` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedSpectrumEntropyUpper.lean (declaration OAI.InvariantIsing.finiteSpectrum_restrictedPressure_entropy_upper)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tilted
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_restrictedPressure_entropy_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (C : (k : ℕ) → Finset (Spin (N k))) (hC : ∀ k, (C k).Nonempty)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (d : ℝ) (hd : 0 < d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (S : ℝ) (hS : ∀ H ε : ℝ, 0<ε → ∀ᶠ k in atTop,
      ∀ (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i), (∑ i, a i) ≤ H →
        constrainedBlockValue (C k) (contactFieldStep cut hc hfirst hlast a ha)+
          fieldPairing trial (contactFieldStep cut hc hfirst hlast a ha)/2 ≤ S+ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        restrictedRotatedPressure (C k) (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      S + spectralFunctional (finiteR ρ lam hρpos hρsum) trial + ε := by
  sorry

end InvariantIsing

end

end OAI
end
