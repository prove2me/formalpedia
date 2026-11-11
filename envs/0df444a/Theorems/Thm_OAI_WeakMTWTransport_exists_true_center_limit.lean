-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_true_center_limit
-- name    : OAI.WeakMTWTransport.exists_true_center_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:58:16.423121+00:00
-- url     : https://prove2.me/theorems/e177daba-463f-4964-b4c4-bd84190c75d6
-- title:
--   OAI.WeakMTWTransport.exists_true_center_limit: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_true_center_limit` of [lean/OAI/Analysis/BiholderTransport/Regularity/TrueCenterLimit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/TrueCenterLimit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma exists_true_center_limit : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
--       ∀(u:M → ℝ) (a c:M) (φ:ℕ → ℝ → ℝ) (lj:ℕ → ℝ),
--       ∀J:(j:ℕ) → TrueCenterJet (n:=n) u a c (φ j) (lj j),
--       ∀(l κ χ:ℝ) (q r:Model n) (H:Model n →L[ℝ] Model n →L[ℝ] ℝ),
--       l∈U → 0<l → l<1 → 0<χ →
--       (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a →
--       Tendsto lj atTop (𝓝 l) →
--       Tendsto (fun j=>(J j).b) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
--       Tendsto (fun j=>(J j).q) atTop (𝓝 q) →
--       Tendsto (fun j=>(J j).fullRay) atTop (𝓝 (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
--       Tendsto (fun j=>(J j).curvature) atTop (𝓝 κ) →
--       Tendsto (fun j=>(J j).matrix) atTop (𝓝 H) →
--       (∀ᶠ j in atTop,χ≤expJacobian (J j).y (J j).p*
--         (normalHessianOperator (J j).y (J j).p+(J j).A).det) →
--       ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
--         (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
--         (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
--           (κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤H d d) ∧
--         0<expJacobian c r ∧
--         (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
--           (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.chartFiberInverse` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.bilinearOperator` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.expJacobian` and `OAI.WeakMTWTransport.frameMetric` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.TrueCenterJet`, `OAI.WeakMTWTransport.normalHessianOperator`, `OAI.WeakMTWTransport.TrueCenterJet.curvature`, `OAI.WeakMTWTransport.TrueCenterJet.fullRay` and `OAI.WeakMTWTransport.TrueCenterJet.matrix` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.injectivityDomain` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_maximum_true_center` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/TrueCenterLimit.lean (declaration OAI.WeakMTWTransport.exists_true_center_limit)

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
import Definitions.Def_OAIQ232A016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TrueCenterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance trueLimitFinite_r64528c_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
attribute [local instance] OAI.WeakMTWTransport.trueLimitDualGroup
attribute [local instance] OAI.WeakMTWTransport.trueLimitDualSpace
local instance trueLimitBilinearGroup_r64528c_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance trueLimitBilinearSpace_r64528c_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma exists_true_center_limit : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(u:M → ℝ) (a c:M) (φ:ℕ → ℝ → ℝ) (lj:ℕ → ℝ),
    ∀J:(j:ℕ) → TrueCenterJet (n:=n) u a c (φ j) (lj j),
    ∀(l κ χ:ℝ) (q r:Model n) (H:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    l∈U → 0<l → l<1 → 0<χ →
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a →
    Tendsto lj atTop (𝓝 l) →
    Tendsto (fun j=>(J j).b) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
    Tendsto (fun j=>(J j).q) atTop (𝓝 q) →
    Tendsto (fun j=>(J j).fullRay) atTop (𝓝 (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto (fun j=>(J j).curvature) atTop (𝓝 κ) →
    Tendsto (fun j=>(J j).matrix) atTop (𝓝 H) →
    (∀ᶠ j in atTop,χ≤expJacobian (J j).y (J j).p*
      (normalHessianOperator (J j).y (J j).p+(J j).A).det) →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤H d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  sorry
end TrueCenterLimit
end WeakMTWTransport

end
end

end OAI
end
