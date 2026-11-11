-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_normal_test_to_chart
-- name    : OAI.WeakMTWTransport.normal_test_to_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:55:56.653764+00:00
-- url     : https://prove2.me/theorems/84ca4f3f-e202-4a3c-836d-aac8f93b3f18
-- title:
--   OAI.WeakMTWTransport.normal_test_to_chart: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.normal_test_to_chart` of [lean/OAI/Analysis/BiholderTransport/Coordinates/NormalTestChart.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/NormalTestChart.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma normal_test_to_chart {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
--       (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) (hp:p∈injectivityDomain x)
--       {u:M → ℝ} {φ:TangentSpace 𝓘(ℝ,Model n) x → ℝ}
--       (hφ:ContDiffAt ℝ 2 φ 0) (hφD:fderiv ℝ φ 0=innerSL ℝ p)
--       (hval:u x=φ 0) (hlo:∀ᶠ w in 𝓝 0,φ w≤u (riemannianExp x w))
--       (hpos:∃m>0,∀d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue x p d) :
--       let z:=extChartAt 𝓘(ℝ,Model n) a x
--       ∃ψ:Model n → ℝ,∃R:Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
--         ContDiffAt ℝ 2 ψ z ∧
--         chartGradientVector a z (fderiv ℝ ψ z)∈injectivityDomain
--           ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
--         coordinateBackward a (-1,z,fderiv ℝ ψ z)=riemannianExp x p ∧
--         u ((extChartAt 𝓘(ℝ,Model n) a).symm z)=ψ z ∧
--         (∀ᶠ w in 𝓝 z,ψ w≤u ((extChartAt 𝓘(ℝ,Model n) a).symm w)) ∧
--         (∃k>0,∀d:Model n,k*‖d‖^2≤fderiv ℝ (fderiv ℝ ψ) z d d+
--           fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z d d) ∧
--         chartJacobian (n:=n) a x*R.toLinearMap.normDet=1 ∧
--         bilinearOperator (fderiv ℝ (fderiv ℝ ψ) z+
--           fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z)=
--           R.adjoint.comp ((bilinearOperator
--             (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)).comp R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.coordinateBackward` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.hessianValue` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.chartCost` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.bilinearOperator` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.chartGradientVector` and `OAI.WeakMTWTransport.chartJacobian` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.normalTestFinite` (definitions bundle `OAIQ232A012` of this split); `OAI.WeakMTWTransport.normalHessian` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/NormalTestChart.lean (declaration OAI.WeakMTWTransport.normal_test_to_chart)

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

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section NormalTestChart
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.normalTestFinite
omit [Nonempty M] in
lemma normal_test_to_chart {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) (hp:p∈injectivityDomain x)
    {u:M → ℝ} {φ:TangentSpace 𝓘(ℝ,Model n) x → ℝ}
    (hφ:ContDiffAt ℝ 2 φ 0) (hφD:fderiv ℝ φ 0=innerSL ℝ p)
    (hval:u x=φ 0) (hlo:∀ᶠ w in 𝓝 0,φ w≤u (riemannianExp x w))
    (hpos:∃m>0,∀d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue x p d) :
    let z:=extChartAt 𝓘(ℝ,Model n) a x
    ∃ψ:Model n → ℝ,∃R:Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ 2 ψ z ∧
      chartGradientVector a z (fderiv ℝ ψ z)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      coordinateBackward a (-1,z,fderiv ℝ ψ z)=riemannianExp x p ∧
      u ((extChartAt 𝓘(ℝ,Model n) a).symm z)=ψ z ∧
      (∀ᶠ w in 𝓝 z,ψ w≤u ((extChartAt 𝓘(ℝ,Model n) a).symm w)) ∧
      (∃k>0,∀d:Model n,k*‖d‖^2≤fderiv ℝ (fderiv ℝ ψ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z d d) ∧
      chartJacobian (n:=n) a x*R.toLinearMap.normDet=1 ∧
      bilinearOperator (fderiv ℝ (fderiv ℝ ψ) z+
        fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z)=
        R.adjoint.comp ((bilinearOperator
          (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)).comp R) := by
  sorry

end NormalTestChart
end WeakMTWTransport

end
end

end OAI
end
