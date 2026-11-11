-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_modified_outer_neighborhood
-- name    : OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:59:39.381444+00:00
-- url     : https://prove2.me/theorems/acae12d7-a471-4e8d-8e25-ca0808bd8ffa
-- title:
--   OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood` of [lean/OAI/Analysis/BiholderTransport/Regularity/ModifiedOuterNeighborhood.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/ModifiedOuterNeighborhood.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.modified_outer_neighborhood (hmtw:WeakMTW (n := n) (M := M))
--       {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
--       {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
--       {Φ:ℝ×ℝ → ℝ} (hΦ:ContDiff ℝ ∞ Φ) {β:ℝ} (hmono:StrictMono (fun s=>Φ (β,s)))
--       {a:M} {p:Model n}
--       (ha:p∈activeLogs (fun y=>Φ (β,uv.2 y)) a)
--       (hslope:1 < deriv (fun s=>Φ (β,s)) (uv.2 (riemannianExp a p)))
--       (hcurve:iteratedDeriv 2 (fun s=>Φ (β,s)) (uv.2 (riemannianExp a p)) < 0) :
--       ∃V:Set ((Model n×Model n)×ℝ),V∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),β) ∧
--         ∃C≥0,∀q∈V,StrictMono (fun s=>Φ (q.2,s)) →
--         ∀B:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀d,0 ≤ B d d) →
--         HasLowerSecondTaylor (fun d=>Φ (q.2,uv.2 (movingNormal a (q.1.1,q.1.2+d)))+
--           ‖chartFiberInverse a q.1.1 (q.1.2+d)‖^2/2) 0 B →
--         ∀d,B d d ≤ C*‖d‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor`, `OAI.WeakMTWTransport.activeLogs`, `OAI.WeakMTWTransport.chartFiberInverse` and `OAI.WeakMTWTransport.movingNormal` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/ModifiedOuterNeighborhood.lean (declaration OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood)

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
import Definitions.Def_OAIQ232A017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ModifiedOuterNeighborhood
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.modified_outer_neighborhood (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {Φ:ℝ×ℝ → ℝ} (hΦ:ContDiff ℝ ∞ Φ) {β:ℝ} (hmono:StrictMono (fun s=>Φ (β,s)))
    {a:M} {p:Model n}
    (ha:p∈activeLogs (fun y=>Φ (β,uv.2 y)) a)
    (hslope:1 < deriv (fun s=>Φ (β,s)) (uv.2 (riemannianExp a p)))
    (hcurve:iteratedDeriv 2 (fun s=>Φ (β,s)) (uv.2 (riemannianExp a p)) < 0) :
    ∃V:Set ((Model n×Model n)×ℝ),V∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,(p:Model n)),β) ∧
      ∃C≥0,∀q∈V,StrictMono (fun s=>Φ (q.2,s)) →
      ∀B:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>Φ (q.2,uv.2 (movingNormal a (q.1.1,q.1.2+d)))+
        ‖chartFiberInverse a q.1.1 (q.1.2+d)‖^2/2) 0 B →
      ∀d,B d d ≤ C*‖d‖^2 := by
  sorry

end ModifiedOuterNeighborhood
end WeakMTWTransport

end
end

end OAI
end
