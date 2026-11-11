-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumFamily_eventually_jensen_first
-- name    : OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:13.482516+00:00
-- url     : https://prove2.me/theorems/1f0964aa-8e78-4552-b149-a8f873802632
-- title:
--   OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first` of [lean/OAI/Analysis/BiholderTransport/Convexity/MaximumJensenFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/MaximumJensenFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Metric Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma MaximumFamily.eventually_jensen_first (hmtw : WeakMTW (n := n) (M := M))
--       {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
--       {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo)
--       (hΦ : ContDiff ℝ ∞ (fun p:ℝ×ℝ=>p.2+p.1*Bc ((p.2-α)/D)))
--       (hmono : ∀ b∈Icc bminus bplus,Monotone (fun s=>s+b*Bc ((s-α)/D))) {Lφ : ℝ≥0}
--       (hLip : ∀ b∈Icc bminus bplus,LipschitzWith Lφ (fun s=>s+b*Bc ((s-α)/D)))
--       {A B : ℝ} (hbound : ∀ y,v y∈Icc A B)
--       (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
--       {Q:TangentBundle 𝓘(ℝ,Model n) M}
--       (hQ : Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 Q)) {N:Set (Model n)} (hN : volume N=0) :
--       ∃ K:ℕ,Nonempty (MaximumJensenFamily hmtw hv ho (F.comp (fun k=>k+K) (tendsto_add_atTop_nat K))
--         Q.1 (riemannianExp Q.1 Q.2) N)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.IsCostDualPair`, `OAI.WeakMTWTransport.cTransform` and `OAI.WeakMTWTransport.subgradientGraph` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.MaximumFamily.comp` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.MaximumJensenFamily` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/MaximumJensenFamily.lean (declaration OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first)

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
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumFamily.eventually_jensen_first (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo)
    (hΦ : ContDiff ℝ ∞ (fun p:ℝ×ℝ=>p.2+p.1*Bc ((p.2-α)/D)))
    (hmono : ∀ b∈Icc bminus bplus,Monotone (fun s=>s+b*Bc ((s-α)/D))) {Lφ : ℝ≥0}
    (hLip : ∀ b∈Icc bminus bplus,LipschitzWith Lφ (fun s=>s+b*Bc ((s-α)/D)))
    {A B : ℝ} (hbound : ∀ y,v y∈Icc A B)
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
    {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 Q)) {N:Set (Model n)} (hN : volume N=0) :
    ∃ K:ℕ,Nonempty (MaximumJensenFamily hmtw hv ho (F.comp (fun k=>k+K) (tendsto_add_atTop_nat K))
      Q.1 (riemannianExp Q.1 Q.2) N) := by
  sorry

end WeakMTWTransport

end

end OAI
end
