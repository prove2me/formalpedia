-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_jensen_undo_short
-- name    : OAI.WeakMTWTransport.WeakMTW.jensen_undo_short
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:51:53.649276+00:00
-- url     : https://prove2.me/theorems/26dbb3b3-0f0e-45bc-8d88-dec55209ce9a
-- title:
--   OAI.WeakMTWTransport.WeakMTW.jensen_undo_short: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.jensen_undo_short` of [lean/OAI/Analysis/BiholderTransport/Convexity/JensenUndoShort.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/JensenUndoShort.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma WeakMTW.jensen_undo_short (hmtw:WeakMTW (n:=n) (M:=M))
--       {u v:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
--       (hdual:IsCostDualPair u v) {φ:ℕ → ℝ → ℝ} (hφ:∀k,ContDiff ℝ ∞ (φ k))
--       (hslope:∀k,∀y:M,0<deriv (φ k) (v y) ∧ deriv (φ k) (v y)<1)
--       {a:M} {N:Set (Model n)} {t:ℕ → ℝ} (ht:∀k,0<t k) (ht1:∀k,t k<1)
--       {w:ℕ → M → ℝ} {c:ℕ → M}
--       (J:∀k,JensenSamplesAt (w k) (fun y=>φ k (v y)) (t k) a (c k) N)
--       (i:ℕ → ℕ) (hti:Tendsto t atTop (𝓝 1))
--       {g:Model n →L[ℝ] ℝ} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
--       (hz:Tendsto (fun k=>(J k).z (i k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
--       (hg:Tendsto (fun k=>fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a)
--         ((J k).z (i k))) atTop (𝓝 g))
--       (hH:Tendsto (fun k=>fderiv ℝ (fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a))
--         ((J k).z (i k))) atTop (𝓝 H))
--       (hexp:∀ᶠ k in atTop,∃p:Model n,∃A:Model n →L[ℝ] Model n,
--         (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
--         HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm
--           (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))+h))) p A)
--       (hsem:∀ᶠ k in atTop,∃r>0,∃K:ℝ,
--         ConvexOn ℝ (Metric.ball (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))) r)
--         (fun q=>φ k (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
--       ∃p:ℕ → Model n,∃A:ℕ → Model n →L[ℝ] Model n,
--         (∀ᶠ k in atTop,(∀d e,inner ℝ (A k d) e=inner ℝ d (A k e)) ∧
--           HasQuadraticExpansion (fun h=>φ k (v ((extChartAt 𝓘(ℝ,Model n) a).symm
--             (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))+h)))) (p k) (A k)) ∧
--         Tendsto (fun k=>(innerSL ℝ).comp (A k)) atTop (𝓝 H) ∧
--         Tendsto (fun k=>fderiv ℝ (fun z=>extChartAt 𝓘(ℝ,Model n) a ((J k).Y z))
--           ((J k).z (i k))) atTop (𝓝 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasQuadraticExpansion` and `OAI.WeakMTWTransport.IsCostDualPair` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.chartCenterEnvelope` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.WeakMTW` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/JensenUndoShort.lean (declaration OAI.WeakMTWTransport.WeakMTW.jensen_undo_short)

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
import Definitions.Def_OAIQ232A013

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.jensen_undo_short (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℕ → ℝ → ℝ} (hφ:∀k,ContDiff ℝ ∞ (φ k))
    (hslope:∀k,∀y:M,0<deriv (φ k) (v y) ∧ deriv (φ k) (v y)<1)
    {a:M} {N:Set (Model n)} {t:ℕ → ℝ} (ht:∀k,0<t k) (ht1:∀k,t k<1)
    {w:ℕ → M → ℝ} {c:ℕ → M}
    (J:∀k,JensenSamplesAt (w k) (fun y=>φ k (v y)) (t k) a (c k) N)
    (i:ℕ → ℕ) (hti:Tendsto t atTop (𝓝 1))
    {g:Model n →L[ℝ] ℝ} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hz:Tendsto (fun k=>(J k).z (i k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hg:Tendsto (fun k=>fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a)
      ((J k).z (i k))) atTop (𝓝 g))
    (hH:Tendsto (fun k=>fderiv ℝ (fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a))
      ((J k).z (i k))) atTop (𝓝 H))
    (hexp:∀ᶠ k in atTop,∃p:Model n,∃A:Model n →L[ℝ] Model n,
      (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm
        (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))+h))) p A)
    (hsem:∀ᶠ k in atTop,∃r>0,∃K:ℝ,
      ConvexOn ℝ (Metric.ball (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))) r)
      (fun q=>φ k (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
    ∃p:ℕ → Model n,∃A:ℕ → Model n →L[ℝ] Model n,
      (∀ᶠ k in atTop,(∀d e,inner ℝ (A k d) e=inner ℝ d (A k e)) ∧
        HasQuadraticExpansion (fun h=>φ k (v ((extChartAt 𝓘(ℝ,Model n) a).symm
          (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))+h)))) (p k) (A k)) ∧
      Tendsto (fun k=>(innerSL ℝ).comp (A k)) atTop (𝓝 H) ∧
      Tendsto (fun k=>fderiv ℝ (fun z=>extChartAt 𝓘(ℝ,Model n) a ((J k).Y z))
        ((J k).z (i k))) atTop (𝓝 1) := by
  sorry
end WeakMTWTransport

end

end OAI
end
