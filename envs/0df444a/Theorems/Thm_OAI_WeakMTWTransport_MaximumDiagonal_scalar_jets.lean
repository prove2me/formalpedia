-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumDiagonal_scalar_jets
-- name    : OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:40:23.057764+00:00
-- url     : https://prove2.me/theorems/0888138f-a3cd-4394-84dc-b5d4f495399e
-- title:
--   OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets` of [lean/OAI/Analysis/BiholderTransport/Calculus/MaximumScalarJets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/MaximumScalarJets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle Metric`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma MaximumDiagonal.scalar_jets
--       {u v:M → ℝ} (hu:Continuous u) {Lv:ℝ≥0} (hv:LipschitzWith Lv v)
--       (hdual:IsCostDualPair u v) {α D bminus bplus A₀ B₀:ℝ} {Bc Bo:ℝ → ℝ}
--       {ho:Continuous Bo} (hBc:ContDiff ℝ ∞ Bc)
--       (hmono:∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s)))
--       (hrange:∀y,v y∈Icc A₀ B₀)
--       (hslope:∀b∈Icc bminus bplus,∀y:M,
--         0<deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y) ∧
--         deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y)<1)
--       {hmtw:WeakMTW (n:=n) (M:=M)}
--       {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo} {a c:M} {N:Set (Model n)}
--       {J:MaximumJensenFamily hmtw hv.continuous ho F a c N}
--       {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
--       {Q:M → Prop} {r:ℝ} (hr:0 < r)
--       (hgood:∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r,z∉N →
--         Q ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
--         ∃p:Model n,∃A:Model n →L[ℝ] Model n,
--           (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
--           HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A)
--       (hx:Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
--         (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
--       (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
--         (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
--       {g:Model n →L[ℝ] ℝ} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
--       (hg:Tendsto (fun k=>fderiv ℝ
--         (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
--           ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g))
--       (hH:Tendsto (fun k=>fderiv ℝ (fderiv ℝ
--         (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
--           ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 H)) :
--       ∃p:ℕ → Model n,∃A:ℕ → Model n →L[ℝ] Model n,
--         (∀ᶠ k in atTop,Q ((J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))) ∧
--           (∀d e,inner ℝ (A k d) e=inner ℝ d (A k e)) ∧
--           HasQuadraticExpansion (fun h=>modifiedScalar α D Bc (F.b k,
--             v ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k)+h)))) (p k) (A k)) ∧
--         Tendsto (fun k=>innerSL ℝ (p k)) atTop (𝓝 g) ∧
--         Tendsto (fun k=>(innerSL ℝ).comp (A k)) atTop (𝓝 H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasQuadraticExpansion` and `OAI.WeakMTWTransport.IsCostDualPair` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.modifiedScalar` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.chartCenterEnvelope` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.MaximumDiagonal`, `OAI.WeakMTWTransport.MaximumJensenFamily`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleCenter` and `OAI.WeakMTWTransport.MaximumJensenFamily.sampleIndex` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.WeakMTW` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_maximum_true_center` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/MaximumScalarJets.lean (declaration OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets)

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

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.maximumScalarDualGroup
attribute [local instance] OAI.WeakMTWTransport.maximumScalarDualSpace
local instance maximumScalarBilinearGroup_rf04f95_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumScalarBilinearSpace_rf04f95_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma MaximumDiagonal.scalar_jets
    {u v:M → ℝ} (hu:Continuous u) {Lv:ℝ≥0} (hv:LipschitzWith Lv v)
    (hdual:IsCostDualPair u v) {α D bminus bplus A₀ B₀:ℝ} {Bc Bo:ℝ → ℝ}
    {ho:Continuous Bo} (hBc:ContDiff ℝ ∞ Bc)
    (hmono:∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s)))
    (hrange:∀y,v y∈Icc A₀ B₀)
    (hslope:∀b∈Icc bminus bplus,∀y:M,
      0<deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y)<1)
    {hmtw:WeakMTW (n:=n) (M:=M)}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo} {a c:M} {N:Set (Model n)}
    {J:MaximumJensenFamily hmtw hv.continuous ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    {Q:M → Prop} {r:ℝ} (hr:0 < r)
    (hgood:∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r,z∉N →
      Q ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A)
    (hx:Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    {g:Model n →L[ℝ] ℝ} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hg:Tendsto (fun k=>fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g))
    (hH:Tendsto (fun k=>fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 H)) :
    ∃p:ℕ → Model n,∃A:ℕ → Model n →L[ℝ] Model n,
      (∀ᶠ k in atTop,Q ((J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))) ∧
        (∀d e,inner ℝ (A k d) e=inner ℝ d (A k e)) ∧
        HasQuadraticExpansion (fun h=>modifiedScalar α D Bc (F.b k,
          v ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k)+h)))) (p k) (A k)) ∧
      Tendsto (fun k=>innerSL ℝ (p k)) atTop (𝓝 g) ∧
      Tendsto (fun k=>(innerSL ℝ).comp (A k)) atTop (𝓝 H) := by
  sorry
end WeakMTWTransport

end

end OAI
end
