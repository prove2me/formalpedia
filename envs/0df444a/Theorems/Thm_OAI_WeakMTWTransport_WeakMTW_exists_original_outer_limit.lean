-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_original_outer_limit
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:58:44.639339+00:00
-- url     : https://prove2.me/theorems/5f0a5c8b-20fc-44dd-9bcd-d3dc2b9baacb
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit` of [lean/OAI/Analysis/BiholderTransport/Regularity/OriginalOuterLimit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/OriginalOuterLimit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_original_outer_limit
--       (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
--       ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (Φ:ℝ×ℝ → ℝ),
--         uv∈densityDualClass (metricVolume n) lam cap x0 → ContDiff ℝ ∞ Φ →
--         ∀(a:M) (bj pj:ℕ → Model n) (γj mj:ℕ → ℝ)
--           (Lj:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ)
--           (γ m l κ:ℝ) (p:Model n) (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
--         (show TangentSpace 𝓘(ℝ,Model n) a from p)∈minimizingVectors a →
--         Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) → Tendsto pj atTop (𝓝 p) →
--         Tendsto γj atTop (𝓝 γ) → Tendsto mj atTop (𝓝 m) → Tendsto Lj atTop (𝓝 L) →
--         deriv (fun s=>Φ (γ,s)) (uv.2 (riemannianExp a p))=l →
--         iteratedDeriv 2 (fun s=>Φ (γ,s)) (uv.2 (riemannianExp a p))=κ →
--         1 < l → κ < 0 →
--         (∀d,d≠0 → 0 < m*L d d-(κ/l^2)*
--           (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) p d)^2) →
--         (∀ᶠ j in atTop,bj j∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
--           StrictMono (fun s=>Φ (γj j,s)) ∧
--           (chartRay a (bj j) (pj j)).2∈activeLogs ((fun s=>Φ (γj j,s)) ∘ uv.2)
--             (chartRay a (bj j) (pj j)).1 ∧
--           0 ≤ mj j ∧ (∀d e,Lj j d e=Lj j e d) ∧ (∀d,0 ≤ Lj j d d) ∧
--           HasLowerSecondTaylor (fun d=>Φ (γj j,uv.2 (movingNormal a (bj j,pj j+d)))+
--             ‖chartFiberInverse a (bj j) (pj j+d)‖^2/2) 0 (mj j • Lj j)) →
--         ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
--           (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
--           (∀d,m*L d d-(κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) p d)^2 ≤ V d d) ∧
--           expJacobian (n:=n) (reverseRay (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
--             (l⁻¹ • (reverseRay (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator V).det ≤
--             (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*
--               (expJacobian (n:=n) a p)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor`, `OAI.WeakMTWTransport.activeLogs`, `OAI.WeakMTWTransport.chartFiberInverse`, `OAI.WeakMTWTransport.minimizingVectors` and `OAI.WeakMTWTransport.movingNormal` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.bilinearOperator` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.chartRay`, `OAI.WeakMTWTransport.expJacobian` and `OAI.WeakMTWTransport.frameMetric` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.densityDualClass` and `OAI.WeakMTWTransport.reverseRay` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/OriginalOuterLimit.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit)

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
section OriginalOuterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance originalOuterFinite_rce139a_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance originalOuterComplete_rce139a_1 (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
attribute [local instance] OAI.WeakMTWTransport.originalOuterDualGroup
attribute [local instance] OAI.WeakMTWTransport.originalOuterDualSpace
local instance originalOuterBilinearGroup_rce139a_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance originalOuterBilinearSpace_rce139a_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma WeakMTW.exists_original_outer_limit
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (Φ:ℝ×ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → ContDiff ℝ ∞ Φ →
      ∀(a:M) (bj pj:ℕ → Model n) (γj mj:ℕ → ℝ)
        (Lj:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ)
        (γ m l κ:ℝ) (p:Model n) (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
      (show TangentSpace 𝓘(ℝ,Model n) a from p)∈minimizingVectors a →
      Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) → Tendsto pj atTop (𝓝 p) →
      Tendsto γj atTop (𝓝 γ) → Tendsto mj atTop (𝓝 m) → Tendsto Lj atTop (𝓝 L) →
      deriv (fun s=>Φ (γ,s)) (uv.2 (riemannianExp a p))=l →
      iteratedDeriv 2 (fun s=>Φ (γ,s)) (uv.2 (riemannianExp a p))=κ →
      1 < l → κ < 0 →
      (∀d,d≠0 → 0 < m*L d d-(κ/l^2)*
        (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) p d)^2) →
      (∀ᶠ j in atTop,bj j∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
        StrictMono (fun s=>Φ (γj j,s)) ∧
        (chartRay a (bj j) (pj j)).2∈activeLogs ((fun s=>Φ (γj j,s)) ∘ uv.2)
          (chartRay a (bj j) (pj j)).1 ∧
        0 ≤ mj j ∧ (∀d e,Lj j d e=Lj j e d) ∧ (∀d,0 ≤ Lj j d d) ∧
        HasLowerSecondTaylor (fun d=>Φ (γj j,uv.2 (movingNormal a (bj j,pj j+d)))+
          ‖chartFiberInverse a (bj j) (pj j+d)‖^2/2) 0 (mj j • Lj j)) →
      ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
        (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
        (∀d,m*L d d-(κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) p d)^2 ≤ V d d) ∧
        expJacobian (n:=n) (reverseRay (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
          (l⁻¹ • (reverseRay (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator V).det ≤
          (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*
            (expJacobian (n:=n) a p)^2 := by
  sorry
end OriginalOuterLimit
end WeakMTWTransport

end
end

end OAI
end
