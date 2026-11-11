-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_maximum_true_center
-- name    : OAI.WeakMTWTransport.exists_maximum_true_center
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:51.44829+00:00
-- url     : https://prove2.me/theorems/7b14dd92-5155-4d90-8ed4-aeec86b96a9a
-- title:
--   OAI.WeakMTWTransport.exists_maximum_true_center: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_maximum_true_center` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTrueCenter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTrueCenter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle Metric`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma exists_maximum_true_center : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
--       ∀(u v:M → ℝ),Continuous u → ∀Lv:ℝ≥0,∀hv:LipschitzWith Lv v,
--       IsCostDualPair u v → ∀(α D bminus bplus A₀ B₀:ℝ) (Bc Bo:ℝ → ℝ),
--       ∀ho:Continuous Bo,ContDiff ℝ ∞ Bc →
--       (∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
--       (∀y,v y∈Icc A₀ B₀) →
--       (∀b∈Icc bminus bplus,∀y:M,0<deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y) ∧
--         deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y)<1) →
--       ∀K:ℝ≥0,(∀b∈Icc bminus bplus,LipschitzWith K (modifiedDatum v α D b Bc)) →
--       ∀hmtw:WeakMTW (n:=n) (M:=M),
--       ∀F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo,
--       ∀(a c:M) (χ:ℝ) (N:Set (Model n)) (r₀:ℝ),0<χ → 0 < r₀ →
--       (∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r₀,z∉N →
--         OriginalCenterGood (n:=n) u χ ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
--         ∃p:Model n,∃A:Model n →L[ℝ] Model n,
--           (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
--           HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A) →
--       ∀J:MaximumJensenFamily hmtw hv.continuous ho F a c N,
--       ∀(ε:ℕ → ℝ) (P:ℕ → ℕ → Prop) (S:MaximumDiagonal J ε P),
--       Tendsto ε atTop (𝓝 0) → ∀(q:Model n) (β l:ℝ),
--       (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
--       Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
--       Tendsto F.b atTop (𝓝 β) → deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l →
--       l∈U → 0<l → l<1 →
--       ∀(g:Model n →L[ℝ] ℝ) (H L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
--       Tendsto (fun k=>fderiv ℝ
--         (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
--           ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g) →
--       Tendsto (fun k=>fderiv ℝ (fderiv ℝ
--         (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
--           ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 H) →
--       Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
--       ∃r:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
--         reverseRay (⟨c,l • r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
--         ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
--         (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
--         (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
--           (iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (v c)/l^2)*
--             (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤L d d) ∧
--         0<expJacobian c r ∧
--         (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
--           (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasQuadraticExpansion`, `OAI.WeakMTWTransport.IsCostDualPair`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.chartFiberInverse`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.minimizingVectors`, `OAI.WeakMTWTransport.subgradientGraph` and `OAI.WeakMTWTransport.ChartFixedPrefixLimit` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.modifiedScalar` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.bilinearOperator` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.MaximumFamily`, `OAI.WeakMTWTransport.chartCenterEnvelope` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum`, `OAI.WeakMTWTransport.expJacobian` and `OAI.WeakMTWTransport.frameMetric` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.OriginalCenterGood` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.reverseRay` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.MaximumDiagonal`, `OAI.WeakMTWTransport.MaximumJensenFamily`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleIndex` and `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTrueCenter.lean (declaration OAI.WeakMTWTransport.exists_maximum_true_center)

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
import Definitions.Def_OAIQ232A030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumTrueCenter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance maximumTrueDualGroup_rce5796_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueDualSpace_rce5796_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueBilinearGroup_rce5796_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueBilinearSpace_rce5796_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
omit [MeasurableSpace M] [BorelSpace M] in
lemma exists_maximum_true_center : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(u v:M → ℝ),Continuous u → ∀Lv:ℝ≥0,∀hv:LipschitzWith Lv v,
    IsCostDualPair u v → ∀(α D bminus bplus A₀ B₀:ℝ) (Bc Bo:ℝ → ℝ),
    ∀ho:Continuous Bo,ContDiff ℝ ∞ Bc →
    (∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    (∀y,v y∈Icc A₀ B₀) →
    (∀b∈Icc bminus bplus,∀y:M,0<deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y)<1) →
    ∀K:ℝ≥0,(∀b∈Icc bminus bplus,LipschitzWith K (modifiedDatum v α D b Bc)) →
    ∀hmtw:WeakMTW (n:=n) (M:=M),
    ∀F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo,
    ∀(a c:M) (χ:ℝ) (N:Set (Model n)) (r₀:ℝ),0<χ → 0 < r₀ →
    (∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r₀,z∉N →
      OriginalCenterGood (n:=n) u χ ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A) →
    ∀J:MaximumJensenFamily hmtw hv.continuous ho F a c N,
    ∀(ε:ℕ → ℝ) (P:ℕ → ℕ → Prop) (S:MaximumDiagonal J ε P),
    Tendsto ε atTop (𝓝 0) → ∀(q:Model n) (β l:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) → deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l →
    l∈U → 0<l → l<1 →
    ∀(g:Model n →L[ℝ] ℝ) (H L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g) →
    Tendsto (fun k=>fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 H) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∃r:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      reverseRay (⟨c,l • r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
      ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (v c)/l^2)*
          (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤L d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  sorry
end MaximumTrueCenter
end WeakMTWTransport

end
end

end OAI
end
