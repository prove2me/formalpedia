-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_chartJetMatrix_normal_identity
-- name    : OAI.WeakMTWTransport.chartJetMatrix_normal_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:54:03.099479+00:00
-- url     : https://prove2.me/theorems/dbfc677b-a195-4e9c-9a32-d84cd592aae1
-- title:
--   OAI.WeakMTWTransport.chartJetMatrix_normal_identity: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.chartJetMatrix_normal_identity` of [lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ChartTrueMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ChartTrueMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma chartJetMatrix_normal_identity {f:M → ℝ} {a c y:M} {b q:Model n}
--       (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target)
--       (hq:chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
--       (hy:movingPrefix a 1 b q=y) (hc:y∈(extChartAt 𝓘(ℝ,Model n) c).source)
--       {r:TangentSpace 𝓘(ℝ,Model n) y} (hr:r∈injectivityDomain y)
--       (hrx:riemannianExp y r=(extChartAt 𝓘(ℝ,Model n) a).symm b)
--       {S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
--       (hS:HasQuadraticExpansion (fun h=>f (riemannianExp y h)) r S)
--       {p:Model n} {A:Model n →L[ℝ] Model n} (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
--       (hAe:HasQuadraticExpansion (fun h=>f ((extChartAt 𝓘(ℝ,Model n) c).symm
--         (extChartAt 𝓘(ℝ,Model n) c y+h))) p A)
--       {R:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b) → TangentSpace 𝓘(ℝ,Model n) y}
--       (hR:DifferentiableAt ℝ R (chartFiberInverse a b q)) (hR0:R (chartFiberInverse a b q)=0)
--       (hRe:∀ᶠ v in 𝓝 (chartFiberInverse a b q),riemannianExp y (R v)=
--         riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) v) :
--       ∀d,chartJetMatrix a c b q (innerSL ℝ p) ((innerSL ℝ).comp A) d d=
--         inner ℝ (S (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)))
--           (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))+
--         normalHessian y r (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
--           (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasQuadraticExpansion`, `OAI.WeakMTWTransport.chartFiberInverse` and `OAI.WeakMTWTransport.movingPrefix` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.chartJetMatrix` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.normalHessian` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_true_center_jet_gain` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ChartTrueMatrix.lean (declaration OAI.WeakMTWTransport.chartJetMatrix_normal_identity)

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

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartTrueMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma chartJetMatrix_normal_identity {f:M → ℝ} {a c y:M} {b q:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hq:chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hy:movingPrefix a 1 b q=y) (hc:y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    {r:TangentSpace 𝓘(ℝ,Model n) y} (hr:r∈injectivityDomain y)
    (hrx:riemannianExp y r=(extChartAt 𝓘(ℝ,Model n) a).symm b)
    {S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hS:HasQuadraticExpansion (fun h=>f (riemannianExp y h)) r S)
    {p:Model n} {A:Model n →L[ℝ] Model n} (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    (hAe:HasQuadraticExpansion (fun h=>f ((extChartAt 𝓘(ℝ,Model n) c).symm
      (extChartAt 𝓘(ℝ,Model n) c y+h))) p A)
    {R:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b) → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R (chartFiberInverse a b q)) (hR0:R (chartFiberInverse a b q)=0)
    (hRe:∀ᶠ v in 𝓝 (chartFiberInverse a b q),riemannianExp y (R v)=
      riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) v) :
    ∀d,chartJetMatrix a c b q (innerSL ℝ p) ((innerSL ℝ).comp A) d d=
      inner ℝ (S (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)))
        (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))+
      normalHessian y r (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
        (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)) := by
  sorry

end ChartTrueMatrix
end WeakMTWTransport

end
end

end OAI
end
