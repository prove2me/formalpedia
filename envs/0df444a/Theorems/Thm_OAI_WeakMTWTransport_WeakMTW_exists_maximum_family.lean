-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_maximum_family
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_maximum_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:47:25.428826+00:00
-- url     : https://prove2.me/theorems/81fa286e-5722-4530-9888-82f1032f0bd4
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_maximum_family: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_maximum_family` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma WeakMTW.exists_maximum_family (hmtw : WeakMTW (n := n) (M := M))
--       {v : M → ℝ} (hv : Continuous v) {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
--       (hc : Continuous Bc) (ho : Continuous Bo) {H : ℝ}
--       (hbound : ∀ s,0≤Bo s ∧ Bo s≤H) (hp : 0<bplus) (hm : 0≤bminus)
--       (hsmall : bminus≤bplus/(64*1024^2))
--       (hupper : ∀ b∈Icc bminus bplus,∀ z,modifiedExcess v α D b Bc Bo z≤b)
--       (hlower : ∃ y,bplus/(8*1024^2)≤ modifiedExcess v α D (bplus/(8*1024)) Bc Bo y)
--       {L : ℝ≥0} (hLip : ∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc))
--       {δ : ℝ} (hδ : 0<δ)
--       (hreg : ∀ b∈Icc bminus bplus,∀ τ:ℝ,0<τ → τ<δ →
--         MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (modifiedDatum v α D b Bc))) :
--       Nonempty (MaximumFamily (n := n) v α D bminus bplus Bc Bo)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.hopfLax` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.modifiedExcess` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.WeakMTW` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.class_power` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumFamily.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_maximum_family)

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
import Definitions.Def_OAIQ232A007

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

lemma WeakMTW.exists_maximum_family (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (hc : Continuous Bc) (ho : Continuous Bo) {H : ℝ}
    (hbound : ∀ s,0≤Bo s ∧ Bo s≤H) (hp : 0<bplus) (hm : 0≤bminus)
    (hsmall : bminus≤bplus/(64*1024^2))
    (hupper : ∀ b∈Icc bminus bplus,∀ z,modifiedExcess v α D b Bc Bo z≤b)
    (hlower : ∃ y,bplus/(8*1024^2)≤ modifiedExcess v α D (bplus/(8*1024)) Bc Bo y)
    {L : ℝ≥0} (hLip : ∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc))
    {δ : ℝ} (hδ : 0<δ)
    (hreg : ∀ b∈Icc bminus bplus,∀ τ:ℝ,0<τ → τ<δ →
      MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (modifiedDatum v α D b Bc))) :
    Nonempty (MaximumFamily (n := n) v α D bminus bplus Bc Bo) := by
  sorry
end WeakMTWTransport

end

end OAI
end
