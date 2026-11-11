-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_uniform_intrinsic_contact_bounds
-- name    : OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:55:02.619479+00:00
-- url     : https://prove2.me/theorems/cb203b81-adce-4062-b50d-f264327ab3f2
-- title:
--   OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds` of [lean/OAI/Analysis/BiholderTransport/Contact/IntrinsicCEMS.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Contact/IntrinsicCEMS.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter MeasureTheory Manifold Bundle Metric`, `open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction`):
--
--   ```lean
--   lemma exists_uniform_intrinsic_contact_bounds {ell upper : ℝ} (hell : 0<ell)
--       (hupper : 0<upper) :
--       ∃ chi eta : ℝ, 0 < chi ∧ 0<eta ∧ ∀ (v : M → ℝ) (hv : Continuous v)
--         (G : Set M), MeasurableSet G → (∀ᵐ x ∂metricVolume n, x∈G) →
--         (∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) →
--         InjOn (contactSelection hv) G →
--         (∀ x∈G, ∃ p A, NormalAlexandrovContact (n := n) v x p A) →
--         (∀ B : Set M, MeasurableSet B → B⊆G →
--           ENNReal.ofReal ell*metricVolume n B≤ metricVolume n (contactSelection hv '' B) ∧
--           metricVolume n (contactSelection hv '' B)≤ENNReal.ofReal upper*metricVolume n B) →
--         ∀ᵐ x ∂metricVolume n, ∃ p A,
--           NormalAlexandrovContact (n := n) v x p A ∧
--           (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
--           chi≤expJacobian (n := n) x p*|(normalHessianOperator x p+A).det| ∧
--           expJacobian (n := n) x p*|(normalHessianOperator x p+A).det|≤eta
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.cTransform` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.NormalAlexandrovContact` and `OAI.WeakMTWTransport.expJacobian` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.contactSelection` and `OAI.WeakMTWTransport.normalHessianOperator` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.metricVolume` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_density_original_center_good` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Contact/IntrinsicCEMS.lean (declaration OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds)

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A016

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section IntrinsicCEMS
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_3
lemma exists_uniform_intrinsic_contact_bounds {ell upper : ℝ} (hell : 0<ell)
    (hupper : 0<upper) :
    ∃ chi eta : ℝ, 0 < chi ∧ 0<eta ∧ ∀ (v : M → ℝ) (hv : Continuous v)
      (G : Set M), MeasurableSet G → (∀ᵐ x ∂metricVolume n, x∈G) →
      (∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) →
      InjOn (contactSelection hv) G →
      (∀ x∈G, ∃ p A, NormalAlexandrovContact (n := n) v x p A) →
      (∀ B : Set M, MeasurableSet B → B⊆G →
        ENNReal.ofReal ell*metricVolume n B≤ metricVolume n (contactSelection hv '' B) ∧
        metricVolume n (contactSelection hv '' B)≤ENNReal.ofReal upper*metricVolume n B) →
      ∀ᵐ x ∂metricVolume n, ∃ p A,
        NormalAlexandrovContact (n := n) v x p A ∧
        (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
        chi≤expJacobian (n := n) x p*|(normalHessianOperator x p+A).det| ∧
        expJacobian (n := n) x p*|(normalHessianOperator x p+A).det|≤eta := by
  sorry

end IntrinsicCEMS
end WeakMTWTransport

end

end

end

end OAI
end
