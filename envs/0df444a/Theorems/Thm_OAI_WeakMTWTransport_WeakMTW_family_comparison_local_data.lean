-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_family_comparison_local_data
-- name    : OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:52:27.883869+00:00
-- url     : https://prove2.me/theorems/ebfa48f7-b332-46cf-bacc-6c9dd2b5e3cd
-- title:
--   OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data` of [lean/OAI/Analysis/BiholderTransport/Regularity/FamilyComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/FamilyComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Metric Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma WeakMTW.family_comparison_local_data (hmtw : WeakMTW (n := n) (M := M))
--       {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {Kp : Set P} (hKp : IsCompact Kp)
--       (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) {Lφ : ℝ≥0}
--       (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
--       ∃ R>0,∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
--         ∀ ψ:ℝ → ℝ,Continuous ψ → ∀ τ:ℝ,0<τ → τ<1/2 → τ<δ →
--         ∀ c:M,extChartAt 𝓘(ℝ,Model n) a c∈ball (extChartAt 𝓘(ℝ,Model n) a a) R →
--         let χ := extChartAt 𝓘(ℝ,Model n) a
--         let w := fun y=>ψ (cTransform u y)
--         let g := fun y=>Φ (p,cTransform u y)
--         let F := chartOuterEnvelope w (1-τ) a
--         let G := chartCenterEnvelope g (1-τ) a
--         let pole : Model n → M := chartActualPole w (1-τ) a
--         let χP := extChartAt 𝓘(ℝ,Model n) (pole (χ c))
--         ∃ r>0,∃ JF JG JY JP:ℝ≥0,∃ Y:Model n → M,
--           (∀ z∈ball (χ c) r,DifferentiableAt ℝ F z) ∧
--           (∀ z∈ball (χ c) r,DifferentiableAt ℝ G z) ∧
--           LipschitzOnWith JF (fderiv ℝ F) (ball (χ c) r) ∧
--           LipschitzOnWith JG (fderiv ℝ G) (ball (χ c) r) ∧
--           LipschitzOnWith JY (fun z=>χ (Y z)) (ball (χ c) r) ∧
--           LipschitzOnWith JP (fun z=>χP (pole z)) (ball (χ c) r) ∧
--           ∀ z∈ball (χ c) r,
--             Y z∈χ.source ∧ pole z∈χP.source ∧
--             (∀ y:M,G z=g y+cost y (χ.symm z)/(1-(1-τ)) ↔ y=Y z) ∧
--             F z=cTransform w (pole z)+cost (pole z) (χ.symm z)/(1-τ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.cTransform` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.chartCenterEnvelope` and `OAI.WeakMTWTransport.chartOuterEnvelope` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.chartActualPole` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.cost` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/FamilyComparison.lean (declaration OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data)

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
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma WeakMTW.family_comparison_local_data (hmtw : WeakMTW (n := n) (M := M))
    {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {Kp : Set P} (hKp : IsCompact Kp)
    (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) {Lφ : ℝ≥0}
    (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ R>0,∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ ψ:ℝ → ℝ,Continuous ψ → ∀ τ:ℝ,0<τ → τ<1/2 → τ<δ →
      ∀ c:M,extChartAt 𝓘(ℝ,Model n) a c∈ball (extChartAt 𝓘(ℝ,Model n) a a) R →
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let w := fun y=>ψ (cTransform u y)
      let g := fun y=>Φ (p,cTransform u y)
      let F := chartOuterEnvelope w (1-τ) a
      let G := chartCenterEnvelope g (1-τ) a
      let pole : Model n → M := chartActualPole w (1-τ) a
      let χP := extChartAt 𝓘(ℝ,Model n) (pole (χ c))
      ∃ r>0,∃ JF JG JY JP:ℝ≥0,∃ Y:Model n → M,
        (∀ z∈ball (χ c) r,DifferentiableAt ℝ F z) ∧
        (∀ z∈ball (χ c) r,DifferentiableAt ℝ G z) ∧
        LipschitzOnWith JF (fderiv ℝ F) (ball (χ c) r) ∧
        LipschitzOnWith JG (fderiv ℝ G) (ball (χ c) r) ∧
        LipschitzOnWith JY (fun z=>χ (Y z)) (ball (χ c) r) ∧
        LipschitzOnWith JP (fun z=>χP (pole z)) (ball (χ c) r) ∧
        ∀ z∈ball (χ c) r,
          Y z∈χ.source ∧ pole z∈χP.source ∧
          (∀ y:M,G z=g y+cost y (χ.symm z)/(1-(1-τ)) ↔ y=Y z) ∧
          F z=cTransform w (pole z)+cost (pole z) (χ.symm z)/(1-τ) := by
  sorry
end WeakMTWTransport

end

end OAI
end
