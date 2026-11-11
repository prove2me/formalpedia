-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actual_sample_pole_matrix
-- name    : OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:51:14.8533+00:00
-- url     : https://prove2.me/theorems/6e5dfffe-9f00-4efe-b643-4dd475e2d1f8
-- title:
--   OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix` of [lean/OAI/Analysis/BiholderTransport/Calculus/SampleJetData.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/SampleJetData.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma WeakMTW.actual_sample_pole_matrix (hmtw : WeakMTW (n := n) (M := M))
--       {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
--       {x a c : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
--       (hp : p∈normalSubdifferential (n := n) (cTransform v) x)
--       (hz : riemannianExp x (t • p)∈(extChartAt 𝓘(ℝ,Model n) a).source)
--       (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).source)
--       (hD : DifferentiableAt ℝ
--         (fun w : Model n => extChartAt 𝓘(ℝ,Model n) c
--           (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm w)))
--         (extChartAt 𝓘(ℝ,Model n) a (riemannianExp x (t • p)))) :
--       let V := TangentSpace 𝓘(ℝ,Model n) x
--       let I : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
--       let L : V →L[ℝ] V →L[ℝ] ℝ := t • I - fderiv ℝ (fderiv ℝ
--         (fun q:V=>hopfLax t (cTransform v) (riemannianExp x (t • q)))) p
--       DifferentiableAt ℝ (fderiv ℝ
--         (fun q:V=>hopfLax t (cTransform v) (riemannianExp x (t • q)))) p ∧
--       (∀ d:V,0≤L d d) ∧ (∀ d e:V,L d e=L e d) ∧
--       (∀ q∈activeLogs v x,∀ d:V,L (q-p) d=0) ∧
--       (∀ (ι:Type) [Fintype ι] (pj:ι → V) (w:ι → ℝ),
--         (∀ j,0≤w j) → (∑ j,w j=1) → (∑ j,w j • pj j=p) →
--         (∀ j,pj j∈activeLogs v x) → ∀ i,0<w i →
--         HasLowerSecondTaylor (fun d:V=>v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2)
--           0 (w i • L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor`, `OAI.WeakMTWTransport.activeLogs`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.hopfLax` and `OAI.WeakMTWTransport.normalSubdifferential` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.hopfPole` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/SampleJetData.lean (declaration OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix)

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
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.actual_sample_pole_matrix (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {x a c : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈normalSubdifferential (n := n) (cTransform v) x)
    (hz : riemannianExp x (t • p)∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hD : DifferentiableAt ℝ
      (fun w : Model n => extChartAt 𝓘(ℝ,Model n) c
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm w)))
      (extChartAt 𝓘(ℝ,Model n) a (riemannianExp x (t • p)))) :
    let V := TangentSpace 𝓘(ℝ,Model n) x
    let I : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
    let L : V →L[ℝ] V →L[ℝ] ℝ := t • I - fderiv ℝ (fderiv ℝ
      (fun q:V=>hopfLax t (cTransform v) (riemannianExp x (t • q)))) p
    DifferentiableAt ℝ (fderiv ℝ
      (fun q:V=>hopfLax t (cTransform v) (riemannianExp x (t • q)))) p ∧
    (∀ d:V,0≤L d d) ∧ (∀ d e:V,L d e=L e d) ∧
    (∀ q∈activeLogs v x,∀ d:V,L (q-p) d=0) ∧
    (∀ (ι:Type) [Fintype ι] (pj:ι → V) (w:ι → ℝ),
      (∀ j,0≤w j) → (∑ j,w j=1) → (∑ j,w j • pj j=p) →
      (∀ j,pj j∈activeLogs v x) → ∀ i,0<w i →
      HasLowerSecondTaylor (fun d:V=>v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2)
        0 (w i • L)) := by
  sorry

end WeakMTWTransport

end

end OAI
end
