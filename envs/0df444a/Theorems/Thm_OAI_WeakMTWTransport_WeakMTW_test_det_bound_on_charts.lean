-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_test_det_bound_on_charts
-- name    : OAI.WeakMTWTransport.WeakMTW.test_det_bound_on_charts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:02:14.03852+00:00
-- url     : https://prove2.me/theorems/871b69b5-d3fb-4646-a222-27b05937210c
-- title:
--   OAI.WeakMTWTransport.WeakMTW.test_det_bound_on_charts: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.test_det_bound_on_charts` of [lean/OAI/Analysis/BiholderTransport/Regularity/UniformTestDet.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/UniformTestDet.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction NNReal`):
--
--   ```lean
--   lemma WeakMTW.test_det_bound_on_charts
--       (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
--       (hlam : 0 < lam) (hcap : 0 ≤ cap) {a b : M} {U V : Set M}
--       (hU : IsOpen U) (hUa : U⊆(extChartAt 𝓘(ℝ,Model n) a).source)
--       (hV : IsOpen V) (hVb : V⊆(extChartAt 𝓘(ℝ,Model n) b).source)
--       {C D : ℝ≥0} (hD : LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
--         ((extChartAt 𝓘(ℝ,Model n) a) '' U))
--       (hC : LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) b) V)
--       {z : Model n} (hz : z∈(extChartAt 𝓘(ℝ,Model n) a) '' U)
--       {x0 : M} {uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)}
--       (huv : uv∈densityDualClass (metricVolume n) lam cap x0)
--       {φ : Model n → ℝ} (hφ : ContDiffAt ℝ 2 φ z)
--       (hYz : coordinateBackward a (-1,z,fderiv ℝ φ z)∈V)
--       (hpφ : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
--         ((extChartAt 𝓘(ℝ,Model n) a).symm z))
--       (hval : uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z)
--       (hlo : ∀ᶠ w in 𝓝 z,φ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w))
--       (hpos : ∃ m>0,∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
--         fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) :
--       |(fderiv ℝ (chartTestContact a b φ) z).det|≤(cap/lam)*((C:ℝ)*(D:ℝ))^n
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.coordinateBackward` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.chartCost` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.chartGradientVector` and `OAI.WeakMTWTransport.chartTestContact` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.metricVolume` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/UniformTestDet.lean (declaration OAI.WeakMTWTransport.WeakMTW.test_det_bound_on_charts)

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
open scoped Topology ContDiff BoundedContinuousFunction NNReal

namespace WeakMTWTransport
section UniformTestDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.uTDualGroup
attribute [local instance] OAI.WeakMTWTransport.uTDualSpace
local instance uTBilinGroup_r597ac7_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance uTBilinSpace_r597ac7_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.WeakMTWTransport.uTPairGroup
attribute [local instance] OAI.WeakMTWTransport.uTPairSpace
local instance uTMapGroup_r597ac7_1 : NormedAddCommGroup (Model n →L[ℝ] Model n × (Model n →L[ℝ] ℝ)) := inferInstance
local instance uTMapSpace_r597ac7_1 : NormedSpace ℝ (Model n →L[ℝ] Model n × (Model n →L[ℝ] ℝ)) := inferInstance
lemma WeakMTW.test_det_bound_on_charts
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) {a b : M} {U V : Set M}
    (hU : IsOpen U) (hUa : U⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hV : IsOpen V) (hVb : V⊆(extChartAt 𝓘(ℝ,Model n) b).source)
    {C D : ℝ≥0} (hD : LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
      ((extChartAt 𝓘(ℝ,Model n) a) '' U))
    (hC : LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) b) V)
    {z : Model n} (hz : z∈(extChartAt 𝓘(ℝ,Model n) a) '' U)
    {x0 : M} {uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)}
    (huv : uv∈densityDualClass (metricVolume n) lam cap x0)
    {φ : Model n → ℝ} (hφ : ContDiffAt ℝ 2 φ z)
    (hYz : coordinateBackward a (-1,z,fderiv ℝ φ z)∈V)
    (hpφ : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hval : uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z)
    (hlo : ∀ᶠ w in 𝓝 z,φ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (hpos : ∃ m>0,∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
      fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) :
    |(fderiv ℝ (chartTestContact a b φ) z).det|≤(cap/lam)*((C:ℝ)*(D:ℝ))^n := by
  sorry

end UniformTestDet
end WeakMTWTransport

end
end

end OAI
end
