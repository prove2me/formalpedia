-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_uniform_intrinsic_test_det_bound
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:59:14.389518+00:00
-- url     : https://prove2.me/theorems/45c2ea1f-b679-46b2-a0cc-eb8644548312
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound` of [lean/OAI/Analysis/BiholderTransport/Regularity/IntrinsicTestDet.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/IntrinsicTestDet.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction NNReal`):
--
--   ```lean
--   lemma WeakMTW.exists_uniform_intrinsic_test_det_bound
--       (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ}
--       (hlam:0<lam) (hcap:0 ≤ cap) :
--       ∃ K:ℝ,0<K ∧ ∀ (x0 x:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ))
--         (p:TangentSpace 𝓘(ℝ,Model n) x) (φ:TangentSpace 𝓘(ℝ,Model n) x → ℝ),
--         uv∈densityDualClass (metricVolume n) lam cap x0 → p∈injectivityDomain x →
--         ContDiffAt ℝ 2 φ 0 → fderiv ℝ φ 0=innerSL ℝ p →
--         uv.1 x=φ 0 → (∀ᶠ w in 𝓝 0,φ w≤uv.1 (riemannianExp x w)) →
--         (∃m>0,∀d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue x p d) →
--         expJacobian (n:=n) x p *
--           |(bilinearOperator (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)).det|≤K
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.hessianValue` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.bilinearOperator` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.expJacobian` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.ivFinite` (definitions bundle `OAIQ232A012` of this split); `OAI.WeakMTWTransport.normalHessian` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/IntrinsicTestDet.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound)

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
import Definitions.Def_OAIQ232A017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction NNReal

namespace WeakMTWTransport
section IntrinsicTestDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.ivFinite
lemma WeakMTW.exists_uniform_intrinsic_test_det_bound
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ}
    (hlam:0<lam) (hcap:0 ≤ cap) :
    ∃ K:ℝ,0<K ∧ ∀ (x0 x:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ))
      (p:TangentSpace 𝓘(ℝ,Model n) x) (φ:TangentSpace 𝓘(ℝ,Model n) x → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → p∈injectivityDomain x →
      ContDiffAt ℝ 2 φ 0 → fderiv ℝ φ 0=innerSL ℝ p →
      uv.1 x=φ 0 → (∀ᶠ w in 𝓝 0,φ w≤uv.1 (riemannianExp x w)) →
      (∃m>0,∀d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue x p d) →
      expJacobian (n:=n) x p *
        |(bilinearOperator (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)).det|≤K := by
  sorry

end IntrinsicTestDet
end WeakMTWTransport

end
end

end OAI
end
