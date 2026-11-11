-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_maximum_center_gain
-- name    : OAI.WeakMTWTransport.exists_maximum_center_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:55.717675+00:00
-- url     : https://prove2.me/theorems/2156b048-2883-4f47-8517-1cfcbfeef01e
-- title:
--   OAI.WeakMTWTransport.exists_maximum_center_gain: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_maximum_center_gain` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumCenterLower.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumCenterLower.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma exists_maximum_center_gain :
--       ∃ c0>0,∀ᶠ l:ℝ in 𝓝 1,0<l → l<1 →
--       ∀ (hmtw : WeakMTW (n := n) (M := M)) (u v : M → ℝ),
--       Continuous u → ∀ (Lv : ℝ≥0) (hv : LipschitzWith Lv v),
--       IsCostDualPair u v →
--       ∀ (α D bminus bplus : ℝ) (Bc Bo : ℝ → ℝ) (ho : Continuous Bo),
--       ContDiff ℝ ∞ Bc →
--       (∀ b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
--       ∀ L:ℝ≥0,(∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc)) →
--       ∀ (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo) (a c:M) (N:Set (Model n)),
--       ∀ J : MaximumJensenFamily hmtw hv.continuous ho F a c N,
--       ∀ (q:Model n) (β:ℝ),
--       (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
--       riemannianExp a q=c →
--       Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
--       Tendsto F.b atTop (𝓝 β) →
--       deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l →
--       ∀ ε:ℝ,0<ε → ∀ᶠ k in atTop,∀ d:Model n,
--         c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
--           (iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (v c)/l^2)*
--             (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2 - ε*‖d‖^2 ≤
--             (J.first k).H d d
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.IsCostDualPair`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.minimizingVectors`, `OAI.WeakMTWTransport.subgradientGraph` and `OAI.WeakMTWTransport.ChartFixedPrefixLimit` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.modifiedScalar` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.MaximumJensenFamily` and `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumCenterLower.lean (declaration OAI.WeakMTWTransport.exists_maximum_center_gain)

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
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumCenterLower
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_maximum_center_gain :
    ∃ c0>0,∀ᶠ l:ℝ in 𝓝 1,0<l → l<1 →
    ∀ (hmtw : WeakMTW (n := n) (M := M)) (u v : M → ℝ),
    Continuous u → ∀ (Lv : ℝ≥0) (hv : LipschitzWith Lv v),
    IsCostDualPair u v →
    ∀ (α D bminus bplus : ℝ) (Bc Bo : ℝ → ℝ) (ho : Continuous Bo),
    ContDiff ℝ ∞ Bc →
    (∀ b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    ∀ L:ℝ≥0,(∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc)) →
    ∀ (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo) (a c:M) (N:Set (Model n)),
    ∀ J : MaximumJensenFamily hmtw hv.continuous ho F a c N,
    ∀ (q:Model n) (β:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
    riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) →
    deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l →
    ∀ ε:ℝ,0<ε → ∀ᶠ k in atTop,∀ d:Model n,
      c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        (iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (v c)/l^2)*
          (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2 - ε*‖d‖^2 ≤
          (J.first k).H d d := by
  sorry

end MaximumCenterLower
end WeakMTWTransport

end
end

end OAI
end
