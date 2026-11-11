-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumDiagonal_good_centers
-- name    : OAI.WeakMTWTransport.MaximumDiagonal.good_centers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:46.197404+00:00
-- url     : https://prove2.me/theorems/d490d1c2-8b91-44d2-8d6e-5db42674b4bd
-- title:
--   OAI.WeakMTWTransport.MaximumDiagonal.good_centers: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumDiagonal.good_centers` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumGoodCenters.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumGoodCenters.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma MaximumDiagonal.good_centers {J:MaximumJensenFamily hmtw hv ho F a c N}
--       {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P) (hBc:Continuous Bc)
--       (hx:Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
--       (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
--         (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
--       {C:ℝ} (hG:∀ᶠ k in atTop,∀d,
--         fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
--           ((J.sample k).z (J.sampleIndex k (S.ν k))) d d ≤ C*‖d‖^2) :
--       ∀ᶠ k in atTop,J.sampleCenter k (S.ν k)∉N
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.chartCenterEnvelope` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.MaximumDiagonal`, `OAI.WeakMTWTransport.MaximumJensenFamily`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleCenter` and `OAI.WeakMTWTransport.MaximumJensenFamily.sampleIndex` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.WeakMTW` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumGoodCenters.lean (declaration OAI.WeakMTWTransport.MaximumDiagonal.good_centers)

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
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.good_centers {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P) (hBc:Continuous Bc)
    (hx:Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    {C:ℝ} (hG:∀ᶠ k in atTop,∀d,
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) d d ≤ C*‖d‖^2) :
    ∀ᶠ k in atTop,J.sampleCenter k (S.ν k)∉N := by
  sorry

end WeakMTWTransport

end

end OAI
end
