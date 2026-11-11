-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_contact_selection_chart_differential_full
-- name    : OAI.WeakMTWTransport.contact_selection_chart_differential_full
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:54:10.864431+00:00
-- url     : https://prove2.me/theorems/6bd57a5a-e952-4aaf-95d4-4819d30b9d73
-- title:
--   OAI.WeakMTWTransport.contact_selection_chart_differential_full: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.contact_selection_chart_differential_full` of [lean/OAI/Analysis/BiholderTransport/Contact/ContactCharts2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Contact/ContactCharts2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma contact_selection_chart_differential_full {v : M → ℝ} (hv : Continuous v)
--       {T : M → M} (hT : ∀ z, contactGap (cTransform v) v z (T z)=0)
--       {G : Set M} (hG : ∀ z∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) z)
--       {x : M} (hxG : x∈G) {p : TangentSpace 𝓘(ℝ,Model n) x}
--       (hp : p∈activeLogs (n := n) v x) (hpI : p∈injectivityDomain x)
--       {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
--       (hA : ∀ u w, inner ℝ (A u) w=inner ℝ u (A w))
--       (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A)
--       (a b : M) (hGs : G⊆(extChartAt 𝓘(ℝ,Model n) a).source)
--       (hTxs : T x∈(extChartAt 𝓘(ℝ,Model n) b).source) :
--       ∃ R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
--       ∃ S : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n,
--         HasFDerivWithinAt
--           ((extChartAt 𝓘(ℝ,Model n) b) ∘ T ∘ (extChartAt 𝓘(ℝ,Model n) a).symm)
--           (S.comp ((normalHessianOperator x p+A).comp R))
--           ((extChartAt 𝓘(ℝ,Model n) a) '' G) ((extChartAt 𝓘(ℝ,Model n) a) x) ∧
--         S=fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp (n := n) x) p ∧
--         (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).comp R=
--           ContinuousLinearMap.id ℝ (Model n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasQuadraticExpansion`, `OAI.WeakMTWTransport.activeLogs`, `OAI.WeakMTWTransport.cTransform` and `OAI.WeakMTWTransport.contactGap` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.normalHessianOperator` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Contact/ContactCharts2.lean (declaration OAI.WeakMTWTransport.contact_selection_chart_differential_full)

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
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactCharts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma contact_selection_chart_differential_full {v : M → ℝ} (hv : Continuous v)
    {T : M → M} (hT : ∀ z, contactGap (cTransform v) v z (T z)=0)
    {G : Set M} (hG : ∀ z∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) z)
    {x : M} (hxG : x∈G) {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈activeLogs (n := n) v x) (hpI : p∈injectivityDomain x)
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hA : ∀ u w, inner ℝ (A u) w=inner ℝ u (A w))
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A)
    (a b : M) (hGs : G⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hTxs : T x∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ∃ R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
    ∃ S : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n,
      HasFDerivWithinAt
        ((extChartAt 𝓘(ℝ,Model n) b) ∘ T ∘ (extChartAt 𝓘(ℝ,Model n) a).symm)
        (S.comp ((normalHessianOperator x p+A).comp R))
        ((extChartAt 𝓘(ℝ,Model n) a) '' G) ((extChartAt 𝓘(ℝ,Model n) a) x) ∧
      S=fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp (n := n) x) p ∧
      (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).comp R=
        ContinuousLinearMap.id ℝ (Model n) := by
  sorry

end ContactCharts
end WeakMTWTransport

end

end

end

end OAI
end
