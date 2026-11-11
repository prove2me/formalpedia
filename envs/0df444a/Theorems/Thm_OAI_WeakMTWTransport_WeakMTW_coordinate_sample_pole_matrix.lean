-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_coordinate_sample_pole_matrix
-- name    : OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:53:04.376063+00:00
-- url     : https://prove2.me/theorems/0de9c732-fda7-44f8-8477-2213266edc0b
-- title:
--   OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix` of [lean/OAI/Analysis/BiholderTransport/Coordinates/CoordinatePole.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/CoordinatePole.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma WeakMTW.coordinate_sample_pole_matrix (hmtw : WeakMTW (n := n) (M := M))
--       {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
--       {a c d : M} {b p : Model n}
--       (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
--       (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
--         ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈normalSubdifferential (n := n)
--           (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm b))
--       (hz : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source)
--       (hx : (extChartAt 𝓘(ℝ,Model n) a).symm b∈(extChartAt 𝓘(ℝ,Model n) d).source)
--       (hD : DifferentiableAt ℝ
--         (fun w : Model n => extChartAt 𝓘(ℝ,Model n) d
--           (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
--         (extChartAt 𝓘(ℝ,Model n) c (movingPrefix a t b p))) :
--       let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
--       let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
--       let L := coordinatePoleMatrix a t v b p
--       (∀ r:Model n,0≤L r r) ∧ (∀ r s:Model n,L r s=L s r) ∧
--       (∀ q:Model n,A q∈activeLogs v x → ∀ r:Model n,L (q-p) r=0) ∧
--       (∀ (ι:Type) [Fintype ι] (pj:ι → Model n) (w:ι → ℝ),
--         (∀ j,0≤w j) → (∑ j,w j=1) → (∑ j,w j • pj j=p) →
--         (∀ j,A (pj j)∈activeLogs v x) → ∀ i,0<w i →
--         HasLowerSecondTaylor (fun r:Model n=>v (movingNormal a (b,pj i+r))+
--           ‖A (pj i+r)‖^2/2) 0 (w i • L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor`, `OAI.WeakMTWTransport.activeLogs`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.coordinatePoleMatrix`, `OAI.WeakMTWTransport.movingNormal`, `OAI.WeakMTWTransport.movingPrefix` and `OAI.WeakMTWTransport.normalSubdifferential` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.hopfPole` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.WeakMTW` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proofs of `OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact`, `OAI.WeakMTWTransport.MaximumRow.jensen_first_limit` and `OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous` of this split import it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/CoordinatePole.lean (declaration OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix)

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

lemma WeakMTW.coordinate_sample_pole_matrix (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {a c d : M} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈normalSubdifferential (n := n)
        (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hz : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hx : (extChartAt 𝓘(ℝ,Model n) a).symm b∈(extChartAt 𝓘(ℝ,Model n) d).source)
    (hD : DifferentiableAt ℝ
      (fun w : Model n => extChartAt 𝓘(ℝ,Model n) d
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
      (extChartAt 𝓘(ℝ,Model n) c (movingPrefix a t b p))) :
    let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
    let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
    let L := coordinatePoleMatrix a t v b p
    (∀ r:Model n,0≤L r r) ∧ (∀ r s:Model n,L r s=L s r) ∧
    (∀ q:Model n,A q∈activeLogs v x → ∀ r:Model n,L (q-p) r=0) ∧
    (∀ (ι:Type) [Fintype ι] (pj:ι → Model n) (w:ι → ℝ),
      (∀ j,0≤w j) → (∑ j,w j=1) → (∑ j,w j • pj j=p) →
      (∀ j,A (pj j)∈activeLogs v x) → ∀ i,0<w i →
      HasLowerSecondTaylor (fun r:Model n=>v (movingNormal a (b,pj i+r))+
        ‖A (pj i+r)‖^2/2) 0 (w i • L)) := by
  sorry

end WeakMTWTransport

end

end OAI
end
