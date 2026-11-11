-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_actual_center_sequential_gain
-- name    : OAI.WeakMTWTransport.exists_actual_center_sequential_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:43:27.002121+00:00
-- url     : https://prove2.me/theorems/8651bd3f-cef2-4609-a6a0-d84fcfab2a71
-- title:
--   OAI.WeakMTWTransport.exists_actual_center_sequential_gain: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_actual_center_sequential_gain` of [lean/OAI/Analysis/BiholderTransport/Convexity/ActualCenterSemibound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/ActualCenterSemibound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma exists_actual_center_sequential_gain :
--       ∃ c0>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 →
--         ∀ (a c : M) (u v : M → ℝ) (Φ : ℝ×ℝ → ℝ) (γ : ℝ),
--         Continuous v → ContDiffAt ℝ ∞ Φ (γ,v c) →
--         deriv (fun s=>Φ (γ,s)) (v c)=l →
--         ∀ (γj lj τj tj : ℕ → ℝ) (xj bj qj : ℕ → Model n) (zj : ℕ → M)
--           (F : ℕ → Model n → ℝ),
--         ∀ D : CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F,
--         ∀ (r q : Model n),
--         (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c →
--         (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
--         riemannianExp a q=c →
--         Tendsto γj atTop (𝓝 γ) → Tendsto lj atTop (𝓝 l) →
--         Tendsto τj atTop (𝓝 0) → Tendsto tj atTop (𝓝 1) →
--         Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) →
--         Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
--         Tendsto qj atTop (𝓝 q) → Tendsto (fun i=>(D.row i).r) atTop (𝓝 r) →
--         (∀ᶠ i in atTop,0<τj i) → ∀ L : ℝ≥0,
--         (∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) →
--         ∀ ε : ℝ,0<ε →
--         ∀ᶠ i in atTop,∀ d : Model n,
--           c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
--             (iteratedDeriv 2 (fun s=>Φ (γ,s)) (v c)/l^2)*
--               (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤
--           coordinateCenterMatrix a (tj i) (hopfLax (τj i) (fun y=>Φ (γj i,v y)))
--             (bj i) (qj i) d d
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.CenterSequenceData`, `OAI.WeakMTWTransport.coordinateCenterMatrix`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.minimizingVectors` and `OAI.WeakMTWTransport.TrueCenterRow` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_maximum_center_gain` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/ActualCenterSemibound.lean (declaration OAI.WeakMTWTransport.exists_actual_center_sequential_gain)

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
import Definitions.Def_OAIQ232A000

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
section ActualCenterSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_actual_center_sequential_gain :
    ∃ c0>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 →
      ∀ (a c : M) (u v : M → ℝ) (Φ : ℝ×ℝ → ℝ) (γ : ℝ),
      Continuous v → ContDiffAt ℝ ∞ Φ (γ,v c) →
      deriv (fun s=>Φ (γ,s)) (v c)=l →
      ∀ (γj lj τj tj : ℕ → ℝ) (xj bj qj : ℕ → Model n) (zj : ℕ → M)
        (F : ℕ → Model n → ℝ),
      ∀ D : CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F,
      ∀ (r q : Model n),
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c →
      (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
      riemannianExp a q=c →
      Tendsto γj atTop (𝓝 γ) → Tendsto lj atTop (𝓝 l) →
      Tendsto τj atTop (𝓝 0) → Tendsto tj atTop (𝓝 1) →
      Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) →
      Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
      Tendsto qj atTop (𝓝 q) → Tendsto (fun i=>(D.row i).r) atTop (𝓝 r) →
      (∀ᶠ i in atTop,0<τj i) → ∀ L : ℝ≥0,
      (∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) →
      ∀ ε : ℝ,0<ε →
      ∀ᶠ i in atTop,∀ d : Model n,
        c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
          (iteratedDeriv 2 (fun s=>Φ (γ,s)) (v c)/l^2)*
            (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤
        coordinateCenterMatrix a (tj i) (hopfLax (τj i) (fun y=>Φ (γj i,v y)))
          (bj i) (qj i) d d := by
  sorry

end ActualCenterSemibound
end WeakMTWTransport

end
end

end OAI
end
