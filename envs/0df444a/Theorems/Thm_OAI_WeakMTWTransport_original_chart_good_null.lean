-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_original_chart_good_null
-- name    : OAI.WeakMTWTransport.original_chart_good_null
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:44:24.434794+00:00
-- url     : https://prove2.me/theorems/8cb72367-b17e-49fb-8845-35d6bd09b4d7
-- title:
--   OAI.WeakMTWTransport.original_chart_good_null: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.original_chart_good_null` of [lean/OAI/Analysis/BiholderTransport/Volume/OriginalNullSet.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Volume/OriginalNullSet.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Metric Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   lemma original_chart_good_null {P:M → Prop} (hP:∀ᵐ x ∂metricVolume n,P x)
--       {u v:M → ℝ} (hu:Continuous u) (hdual:IsCostDualPair u v) (a:M) :
--       ∃r>0,∃N:Set (Model n),volume N=0 ∧
--         ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
--         ∀z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,z∉N →
--           P ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
--           ∃p:Model n,∃A:Model n →L[ℝ] Model n,
--             (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
--             HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm (z+h))) p A
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasQuadraticExpansion` and `OAI.WeakMTWTransport.IsCostDualPair` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.metricVolume` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Volume/OriginalNullSet.lean (declaration OAI.WeakMTWTransport.original_chart_good_null)

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
import Definitions.Def_OAIQ232A000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal

namespace WeakMTWTransport
section OriginalNullSet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma original_chart_good_null {P:M → Prop} (hP:∀ᵐ x ∂metricVolume n,P x)
    {u v:M → ℝ} (hu:Continuous u) (hdual:IsCostDualPair u v) (a:M) :
    ∃r>0,∃N:Set (Model n),volume N=0 ∧
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,z∉N →
        P ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
        ∃p:Model n,∃A:Model n →L[ℝ] Model n,
          (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
          HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm (z+h))) p A := by
  sorry
end OriginalNullSet
end WeakMTWTransport

end
end

end OAI
end
