-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumDiagonal_center_matrix_limit
-- name    : OAI.WeakMTWTransport.MaximumDiagonal.center_matrix_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:20.718941+00:00
-- url     : https://prove2.me/theorems/cbfa1f10-e50b-477f-9001-45a0f30c3a03
-- title:
--   OAI.WeakMTWTransport.MaximumDiagonal.center_matrix_limit: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumDiagonal.center_matrix_limit` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumCenterLimit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumCenterLimit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma MaximumDiagonal.center_matrix_limit {J:MaximumJensenFamily hmtw hv ho F a c N}
--       {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
--       (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
--       (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
--       (he:riemannianExp a q=c)
--       (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
--         (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
--       {g:Model n →L[ℝ] ℝ} {B:Model n →L[ℝ] Model n →L[ℝ] ℝ}
--       (hg:Tendsto (fun k=>fderiv ℝ
--         (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
--           ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g))
--       (hB:Tendsto (fun k=>fderiv ℝ (fderiv ℝ
--         (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
--           ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 B)) :
--       Tendsto (fun k=>J.sampleH k (S.ν k)) atTop
--         (𝓝 (chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g B))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.cTransform` and `OAI.WeakMTWTransport.subgradientGraph` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.MaximumFamily`, `OAI.WeakMTWTransport.chartCenterEnvelope` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.chartJetMatrix` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.MaximumDiagonal`, `OAI.WeakMTWTransport.MaximumJensenFamily`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleH` and `OAI.WeakMTWTransport.MaximumJensenFamily.sampleIndex` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_maximum_true_center` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumCenterLimit.lean (declaration OAI.WeakMTWTransport.MaximumDiagonal.center_matrix_limit)

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
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumCenterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.center_matrix_limit {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {g:Model n →L[ℝ] ℝ} {B:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hg:Tendsto (fun k=>fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g))
    (hB:Tendsto (fun k=>fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 B)) :
    Tendsto (fun k=>J.sampleH k (S.ν k)) atTop
      (𝓝 (chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g B)) := by
  sorry

end MaximumCenterLimit
end WeakMTWTransport

end
end

end OAI
end
