-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_strict_test_det_bound
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_strict_test_det_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:02:24.807198+00:00
-- url     : https://prove2.me/theorems/fe4d8372-2c1b-4412-b200-55920a6c436e
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_strict_test_det_bound: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_strict_test_det_bound` of [lean/OAI/Analysis/BiholderTransport/Contact/SmoothTestPDE.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Contact/SmoothTestPDE.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_strict_test_det_bound (hmtw : WeakMTW (n := n) (M := M))
--       {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
--       (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
--         injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a))) :
--       let z := extChartAt 𝓘(ℝ,Model n) a a
--       let b := coordinateBackward a (-1,z,L)
--       ∃ K≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
--         uv∈densityDualClass (metricVolume n) lam cap x0 →
--         ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z → fderiv ℝ φ z=L →
--         uv.1 a=φ z →
--         (∃ ε>0, ∀ᶠ w : Model n in 𝓝 z,
--           ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
--         (∃ m>0, ∀ d : Model n, m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
--           fderiv ℝ (fderiv ℝ (chartCost a b)) z d d) →
--         |(fderiv ℝ (chartTestContact a b φ) z).det|≤K
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.coordinateBackward` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.chartCost` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.chartGradientVector` and `OAI.WeakMTWTransport.chartTestContact` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.metricVolume` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Contact/SmoothTestPDE.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_strict_test_det_bound)

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
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section SmoothTestPDE
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

variable [Nonempty M] [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_strict_test_det_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a))) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    let b := coordinateBackward a (-1,z,L)
    ∃ K≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z → fderiv ℝ φ z=L →
      uv.1 a=φ z →
      (∃ ε>0, ∀ᶠ w : Model n in 𝓝 z,
        ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
      (∃ m>0, ∀ d : Model n, m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d) →
      |(fderiv ℝ (chartTestContact a b φ) z).det|≤K := by
  sorry

end SmoothTestPDE
end WeakMTWTransport

end

end

end

end OAI
end
