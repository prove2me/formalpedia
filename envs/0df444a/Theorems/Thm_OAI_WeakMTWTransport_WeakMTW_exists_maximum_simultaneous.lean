-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_maximum_simultaneous
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:43:03.029257+00:00
-- url     : https://prove2.me/theorems/3695779a-5f9b-479a-abbc-fbe3413ba8d8
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumSimultaneous.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumSimultaneous.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle Metric`, `open scoped Topology ContDiff NNReal BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_maximum_simultaneous
--       (hmtw:WeakMTW (n:=n) (M:=M)) (hn:0 < n) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
--       ∃δ:ℝ,δ>0 ∧ ∃K:ℝ,K>0 ∧ ∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
--       ∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),uv∈densityDualClass (metricVolume n) lam cap x0 →
--       ∀Lv:ℝ≥0,LipschitzWith Lv (uv.2:M → ℝ) → IsCostDualPair (uv.1:M → ℝ) uv.2 →
--       ∀(α D bminus bplus A₀ B₀:ℝ) (Bc Bo:ℝ → ℝ),
--       ∀ho:Continuous Bo,ContDiff ℝ ∞ Bc → ContDiff ℝ ∞ Bo →
--       (∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
--       (∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s))) →
--       (∀y,uv.2 y∈Icc A₀ B₀) →
--       (∀b∈Icc bminus bplus,∀y:M,0 < deriv (fun s=>modifiedScalar α D Bc (b,s)) (uv.2 y) ∧
--         deriv (fun s=>modifiedScalar α D Bc (b,s)) (uv.2 y)<1) →
--       ∀Klip:ℝ≥0,(∀b∈Icc bminus bplus,LipschitzWith Klip (modifiedDatum uv.2 α D b Bc)) →
--       ∀F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo,
--       ∀(a c:M) (χ:ℝ) (N:Set (Model n)) (r₀:ℝ),0 < χ → 0 < r₀ →
--       (∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r₀,z∉N →
--         OriginalCenterGood (n:=n) uv.1 χ ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
--         ∃p:Model n,∃A:Model n →L[ℝ] Model n,
--           (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
--           HasQuadraticExpansion (fun h=>uv.2 ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A) →
--       ∀J:MaximumJensenFamily hmtw uv.2.continuous ho F a c N,
--       ∀(q:Model n) (β l κc:ℝ),
--       (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
--       Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
--       Tendsto F.b atTop (𝓝 β) → deriv (fun s=>modifiedScalar α D Bc (β,s)) (uv.2 c)=l →
--       iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (uv.2 c)=κc →
--       l∈U → 0 < l → l<1 → κc<0 →
--       ∀(r:Fin (Module.finrank ℝ (Model n)+1) → Model n)
--         (m:Fin (Module.finrank ℝ (Model n)+1) → ℝ)
--         (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
--       Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r) →
--       Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m) →
--       Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
--       ∀CH CL:ℝ,0 ≤ CH → 0 ≤ CL →
--       (∀ᶠ k in atTop,∀d,-CH*‖d‖^2 ≤ (J.first k).H d d) →
--       (∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ CL*‖d‖^2) →
--       ∀i,(show TangentSpace 𝓘(ℝ,Model n) a from r i)∈minimizingVectors a →
--       0 < m i → ∀(e:TangentSpace 𝓘(ℝ,Model n) a) (t lo κo:ℝ),
--       ‖e‖=1 → 0 < t → (show TangentSpace 𝓘(ℝ,Model n) a from r i)= (show TangentSpace 𝓘(ℝ,Model n) a from q)+t • e →
--       0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e →
--       deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=lo →
--       iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=κo →
--       1 < lo → κo<0 →
--       ∃rc:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from rc)∈minimizingVectors c ∧
--         reverseRay (⟨c,l • rc⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
--       ∃V W:Model n →L[ℝ] Model n →L[ℝ] ℝ,
--         (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
--         (∀d e,W d e=W e d) ∧ (∀d,d≠0 → 0 < W d d) ∧
--         0 < expJacobian c rc ∧
--         (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
--           (expJacobian a q)^2*χ≤expJacobian c rc*(bilinearOperator V).det ∧
--         expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
--           (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator W).det ≤
--           (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*lo^n*K*
--             (expJacobian (n:=n) a (r i))^2 ∧
--         (-κo/lo^2)*(m i)^(n-1)*(bilinearOperator V).det≤(-κc/l^2)*(bilinearOperator W).det
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasQuadraticExpansion`, `OAI.WeakMTWTransport.IsCostDualPair`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.chartFiberInverse`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.minimizingVectors`, `OAI.WeakMTWTransport.subgradientGraph` and `OAI.WeakMTWTransport.ChartFixedPrefixLimit` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.modifiedScalar` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.bilinearOperator` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum` and `OAI.WeakMTWTransport.expJacobian` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.OriginalCenterGood` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.densityDualClass` and `OAI.WeakMTWTransport.reverseRay` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.MaximumJensenFamily` and `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumSimultaneous.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous)

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

section

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumSimultaneous
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance simulDualGroup_rd89742_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance simulDualSpace_rd89742_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance simulBilinearGroup_rd89742_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance simulBilinearSpace_rd89742_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma WeakMTW.exists_maximum_simultaneous
    (hmtw:WeakMTW (n:=n) (M:=M)) (hn:0 < n) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃δ:ℝ,δ>0 ∧ ∃K:ℝ,K>0 ∧ ∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀Lv:ℝ≥0,LipschitzWith Lv (uv.2:M → ℝ) → IsCostDualPair (uv.1:M → ℝ) uv.2 →
    ∀(α D bminus bplus A₀ B₀:ℝ) (Bc Bo:ℝ → ℝ),
    ∀ho:Continuous Bo,ContDiff ℝ ∞ Bc → ContDiff ℝ ∞ Bo →
    (∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    (∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s))) →
    (∀y,uv.2 y∈Icc A₀ B₀) →
    (∀b∈Icc bminus bplus,∀y:M,0 < deriv (fun s=>modifiedScalar α D Bc (b,s)) (uv.2 y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (uv.2 y)<1) →
    ∀Klip:ℝ≥0,(∀b∈Icc bminus bplus,LipschitzWith Klip (modifiedDatum uv.2 α D b Bc)) →
    ∀F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo,
    ∀(a c:M) (χ:ℝ) (N:Set (Model n)) (r₀:ℝ),0 < χ → 0 < r₀ →
    (∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r₀,z∉N →
      OriginalCenterGood (n:=n) uv.1 χ ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>uv.2 ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A) →
    ∀J:MaximumJensenFamily hmtw uv.2.continuous ho F a c N,
    ∀(q:Model n) (β l κc:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) → deriv (fun s=>modifiedScalar α D Bc (β,s)) (uv.2 c)=l →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (uv.2 c)=κc →
    l∈U → 0 < l → l<1 → κc<0 →
    ∀(r:Fin (Module.finrank ℝ (Model n)+1) → Model n)
      (m:Fin (Module.finrank ℝ (Model n)+1) → ℝ)
      (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r) →
    Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∀CH CL:ℝ,0 ≤ CH → 0 ≤ CL →
    (∀ᶠ k in atTop,∀d,-CH*‖d‖^2 ≤ (J.first k).H d d) →
    (∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ CL*‖d‖^2) →
    ∀i,(show TangentSpace 𝓘(ℝ,Model n) a from r i)∈minimizingVectors a →
    0 < m i → ∀(e:TangentSpace 𝓘(ℝ,Model n) a) (t lo κo:ℝ),
    ‖e‖=1 → 0 < t → (show TangentSpace 𝓘(ℝ,Model n) a from r i)= (show TangentSpace 𝓘(ℝ,Model n) a from q)+t • e →
    0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e →
    deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=lo →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=κo →
    1 < lo → κo<0 →
    ∃rc:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from rc)∈minimizingVectors c ∧
      reverseRay (⟨c,l • rc⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
    ∃V W:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
      (∀d e,W d e=W e d) ∧ (∀d,d≠0 → 0 < W d d) ∧
      0 < expJacobian c rc ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c rc*(bilinearOperator V).det ∧
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator W).det ≤
        (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*lo^n*K*
          (expJacobian (n:=n) a (r i))^2 ∧
      (-κo/lo^2)*(m i)^(n-1)*(bilinearOperator V).det≤(-κc/l^2)*(bilinearOperator W).det := by
  sorry
end MaximumSimultaneous
end WeakMTWTransport

end
end

end OAI
end
