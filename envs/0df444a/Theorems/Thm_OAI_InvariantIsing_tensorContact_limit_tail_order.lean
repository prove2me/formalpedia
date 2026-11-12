-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorContact_limit_tail_order
-- name    : OAI.InvariantIsing.tensorContact_limit_tail_order
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:44:47.32698+00:00
-- url     : https://prove2.me/theorems/1f67c011-2bab-49e9-869a-5ffd11ac05e3
-- title:
--   OAI.InvariantIsing.tensorContact_limit_tail_order: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorContact_limit_tail_order` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorContactTailOrder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorContactTailOrder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem tensorContact_limit_tail_order
--       (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
--       (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
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
--         tensorContactObjective (μ k) (eig k) (c k) (I k) (chainExponent cut)
--           (fun i => (cut i.succ - cut i.castSucc) * values i) S V (p k) ≤
--         tensorContactObjective (μ k) (eig k) (c k) (I k) (chainExponent cut)
--           (fun i => (cut i.succ - cut i.castSucc) * values i) S V q)
--       (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
--       (Q : ProbabilityMeasure (SpectralArray (m + 1)))
--       (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
--         (p k).2.2.1 (p k).2.2.2 (p k).1 n (chainExponent cut) (finiteFieldPath (p k).2.1))
--         atTop (𝓝 Q))
--       (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
--       (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
--       (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
--       (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
--       (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
--       ∀ s ∈ Icc (0 : ℝ) 1, pathTail trial s ≤ pathTail (spectralSpinQuantilePath Q hP hn) s
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralPartitionGeometry` and `OAI.InvariantIsing.TensorContactParameter` (definitions bundle `OAIQ258001` of this split); `OAI.IsingPerceptron.finiteFieldPath` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.pathTail` and `OAI.InvariantIsing.tensorContactRegion` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.spectralSpinQuantilePath`, `OAI.InvariantIsing.tensorContactObjective` and `OAI.InvariantIsing.tensorPerturbedArrayLaw` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.HasEntryGhirlandaGuerra` and `OAI.IsingPerceptron.chainExponent` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.OverlapPath` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.tensorContact_no_positive_minimizing_sequence` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorContactTailOrder.lean (declaration OAI.InvariantIsing.tensorContact_limit_tail_order)

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
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorContact_limit_tail_order
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
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
      tensorContactObjective (μ k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V (p k) ≤
      tensorContactObjective (μ k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V q)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (p k).2.2.1 (p k).2.2.2 (p k).1 n (chainExponent cut) (finiteFieldPath (p k).2.1))
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
