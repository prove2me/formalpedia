-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_parametric_short_lower_sequence
-- name    : OAI.WeakMTWTransport.exists_parametric_short_lower_sequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:51:09.357182+00:00
-- url     : https://prove2.me/theorems/8cc26d9d-26c4-4c9b-bed6-847575562613
-- title:
--   OAI.WeakMTWTransport.exists_parametric_short_lower_sequence: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_parametric_short_lower_sequence` of [lean/OAI/Analysis/BiholderTransport/Regularity/ParametricLowerSequence.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/ParametricLowerSequence.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma exists_parametric_short_lower_sequence {a : M} {ψ : P×Model n → ℝ}
--       {p : P} {x : Model n} (L : ℝ≥0)
--       (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
--       {pj : ℕ → P} {xj : ℕ → Model n} {tj : ℕ → ℝ} {f : ℕ → M → ℝ}
--       (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
--       (ht : Tendsto tj atTop (𝓝 0)) (htpos : ∀ᶠ i in atTop,0<tj i)
--       (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
--       (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) a).symm w))
--       (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) a).symm (xj i))=ψ (pj i,xj i)) :
--       let z := fun i=>parametricShortForward a ψ ((pj i,tj i),xj i)
--       ∃ U : ℕ → Model n → ℝ,
--         (∀ᶠ i in atTop,ContDiffAt ℝ 2 (U i) (z i) ∧
--           U i (z i)=hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm (z i)) ∧
--           ∀ᶠ w in 𝓝 (z i),U i w≤hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w)) ∧
--         Tendsto (fun i=>fderiv ℝ (U i) (z i)) atTop
--           (𝓝 (fderiv ℝ (fun w=>ψ (p,w)) x)) ∧
--         Tendsto (fun i=>fderiv ℝ (fderiv ℝ (U i)) (z i)) atTop
--           (𝓝 (fderiv ℝ (fderiv ℝ (fun w=>ψ (p,w))) x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.hopfLax` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.parametricShortForward` (definitions bundle `OAIQ232A012` of this split); `OAI.WeakMTWTransport.Model` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proofs of `OAI.WeakMTWTransport.parametric_short_center_pole_limit` and `OAI.WeakMTWTransport.parametric_short_pullback_semibound` of this split import it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/ParametricLowerSequence.lean (declaration OAI.WeakMTWTransport.exists_parametric_short_lower_sequence)

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
import Definitions.Def_OAIQ232A012

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
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma exists_parametric_short_lower_sequence {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (ht : Tendsto tj atTop (𝓝 0)) (htpos : ∀ᶠ i in atTop,0<tj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) a).symm (xj i))=ψ (pj i,xj i)) :
    let z := fun i=>parametricShortForward a ψ ((pj i,tj i),xj i)
    ∃ U : ℕ → Model n → ℝ,
      (∀ᶠ i in atTop,ContDiffAt ℝ 2 (U i) (z i) ∧
        U i (z i)=hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm (z i)) ∧
        ∀ᶠ w in 𝓝 (z i),U i w≤hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w)) ∧
      Tendsto (fun i=>fderiv ℝ (U i) (z i)) atTop
        (𝓝 (fderiv ℝ (fun w=>ψ (p,w)) x)) ∧
      Tendsto (fun i=>fderiv ℝ (fderiv ℝ (U i)) (z i)) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ (fun w=>ψ (p,w))) x)) := by
  sorry

end WeakMTWTransport

end

end OAI
end
