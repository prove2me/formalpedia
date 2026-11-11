-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumRow_jensen_first_limit
-- name    : OAI.WeakMTWTransport.MaximumRow.jensen_first_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:38.20124+00:00
-- url     : https://prove2.me/theorems/f0a7d7d1-494a-4b29-bee8-8e8419149b17
-- title:
--   OAI.WeakMTWTransport.MaximumRow.jensen_first_limit: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumRow.jensen_first_limit` of [lean/OAI/Analysis/BiholderTransport/Convexity/MaximumJensen.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/MaximumJensen.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma MaximumRow.jensen_first_limit {v : M → ℝ} {α D b bplus t : ℝ}
--       {Bc Bo : ℝ → ℝ} {z a c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
--       (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
--       (ht : 0<t) (ht1 : t<1) {N : Set (Model n)}
--       (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
--       (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source)
--       (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
--       let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
--       Nonempty (ChartFixedPrefixLimit a (modifiedDatum v α D b Bo)
--         (hopfLax (1-t) (modifiedDatum v α D b Bc)) t
--         (fun k=>e.symm ((extChartAt 𝓘(ℝ,Model n) c).symm (J.z k))) R.q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.ChartFixedPrefixLimit`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.hopfLax` and `OAI.WeakMTWTransport.subgradientGraph` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.WeakMTW` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/MaximumJensen.lean (declaration OAI.WeakMTWTransport.MaximumRow.jensen_first_limit)

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
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumRow.jensen_first_limit {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z a c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
    Nonempty (ChartFixedPrefixLimit a (modifiedDatum v α D b Bo)
      (hopfLax (1-t) (modifiedDatum v α D b Bc)) t
      (fun k=>e.symm ((extChartAt 𝓘(ℝ,Model n) c).symm (J.z k))) R.q) := by
  sorry

end WeakMTWTransport

end

end OAI
end
