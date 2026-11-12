-- Prove2me | Theorems.Thm_OAI_InvariantIsing_spinPriorContact_limit_tail_order
-- name    : OAI.InvariantIsing.spinPriorContact_limit_tail_order
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:43:52.849199+00:00
-- url     : https://prove2.me/theorems/9c42c831-1af2-4b6d-b566-37855155afa0
-- title:
--   OAI.InvariantIsing.spinPriorContact_limit_tail_order: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.spinPriorContact_limit_tail_order` of [lean/OAI/Probability/InvariantIsing/Fields/SpinPriorContactTailOrder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorContactTailOrder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem spinPriorContact_limit_tail_order
--       (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
--       (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
--       (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
--       (eig c : (k : ℕ) → Fin (N k) → ℝ)
--       (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
--       (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
--       (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
--       (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
--       (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
--       (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
--       (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
--       (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
--       (p : (k : ℕ) → TensorContactParameter (N k) m n)
--       (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
--       (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
--         spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
--           (fun i => (cut i.succ - cut i.castSucc) * values i) S V (p k) ≤
--         spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
--           (fun i => (cut i.succ - cut i.castSucc) * values i) S V q)
--       (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
--       (Q : ProbabilityMeasure (SpectralArray (m + 1)))
--       (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) (chainExponent cut) (eig k) (c k) (I k)
--         (p k).2.2.1 (p k).2.2.2 (p k).1 (finiteFieldPath (p k).2.1))
--         atTop (𝓝 Q))
--       (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
--       (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
--       (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
--       (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
--       (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
--       ∀ s ∈ Icc (0 : ℝ) 1, pathTail trial s ≤ pathTail (spectralSpinQuantilePath Q hP hn) s
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralPartitionGeometry` and `OAI.InvariantIsing.TensorContactParameter` (definitions bundle `OAIQ258001` of this split); `OAI.IsingPerceptron.finiteFieldPath` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.pathTail` and `OAI.InvariantIsing.tensorContactRegion` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.spectralSpinQuantilePath`, `OAI.InvariantIsing.spinPriorContactObjective` and `OAI.InvariantIsing.spinPriorPerturbedArrayLaw` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.HasEntryGhirlandaGuerra` and `OAI.IsingPerceptron.chainExponent` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.OverlapPath` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.spinPriorRestrictedContact_entropy_limit` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorContactTailOrder.lean (declaration OAI.InvariantIsing.spinPriorContact_limit_tail_order)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem spinPriorContact_limit_tail_order
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V (p k) ≤
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V q)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) (chainExponent cut) (eig k) (c k) (I k)
      (p k).2.2.1 (p k).2.2.2 (p k).1 (finiteFieldPath (p k).2.1))
      atTop (𝓝 Q))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    ∀ s ∈ Icc (0 : ℝ) 1, pathTail trial s ≤ pathTail (spectralSpinQuantilePath Q hP hn) s := by
  sorry

end InvariantIsing

end

end OAI
end
