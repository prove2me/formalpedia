-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_maximum_true_outer
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:46:31.495451+00:00
-- url     : https://prove2.me/theorems/9984c9b5-8876-49fe-b734-cfc4a23b09c2
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTrueOuter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTrueOuter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_maximum_true_outer
--       (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
--       ∃K>0,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
--       uv∈densityDualClass (metricVolume n) lam cap x0 →
--       ∀(α D bminus bplus:ℝ) (Bc Bo:ℝ → ℝ),∀ho:Continuous Bo,ContDiff ℝ ∞ Bo →
--       (∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s))) →
--       ∀F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo,
--       ∀(a c:M) (N:Set (Model n)),
--       ∀J:MaximumJensenFamily hmtw uv.2.continuous ho F a c N,
--       ∀(ε:ℕ → ℝ),MaximumDiagonal J ε J.OuterSampleGood →
--       Tendsto ε atTop (𝓝 0) → ∀(q:Model n) (β:ℝ),riemannianExp a q=c →
--       Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
--       Tendsto F.b atTop (𝓝 β) →
--       ∀(r:Fin (Module.finrank ℝ (Model n)+1) → Model n)
--         (m:Fin (Module.finrank ℝ (Model n)+1) → ℝ)
--         (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
--       Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r) →
--       Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m) →
--       Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
--       ∀i,(show TangentSpace 𝓘(ℝ,Model n) a from r i)∈minimizingVectors a →
--       0 < m i → ∀l κ:ℝ,
--       deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=l →
--       iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=κ →
--       1 < l → κ < 0 →
--       (∀d,d≠0 → 0 < m i*L d d-(κ/l^2)*
--           (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i) d)^2) →
--       ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
--         (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
--         (∀d,m i*L d d-(κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i) d)^2 ≤ V d d) ∧
--         expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
--           (l⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator V).det ≤
--           (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*
--             (expJacobian (n:=n) a (r i))^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.chartFiberInverse`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.minimizingVectors`, `OAI.WeakMTWTransport.subgradientGraph` and `OAI.WeakMTWTransport.ChartFixedPrefixLimit` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.modifiedScalar` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.bilinearOperator` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum`, `OAI.WeakMTWTransport.expJacobian` and `OAI.WeakMTWTransport.frameMetric` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.densityDualClass` and `OAI.WeakMTWTransport.reverseRay` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.MaximumDiagonal`, `OAI.WeakMTWTransport.MaximumJensenFamily` and `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.MaximumJensenFamily.OuterSampleGood` (definitions bundle `OAIQ232A031` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTrueOuter.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer)

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
import Definitions.Def_OAIQ232A031

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
section MaximumTrueOuter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance maximumOuterFinite_r26318e_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance maximumOuterComplete_r26318e_1 (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
local instance maximumOuterDualGroup_r26318e_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterDualSpace_r26318e_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterBilinearGroup_r26318e_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterBilinearSpace_r26318e_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma WeakMTW.exists_maximum_true_outer
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
    uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀(α D bminus bplus:ℝ) (Bc Bo:ℝ → ℝ),∀ho:Continuous Bo,ContDiff ℝ ∞ Bo →
    (∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s))) →
    ∀F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo,
    ∀(a c:M) (N:Set (Model n)),
    ∀J:MaximumJensenFamily hmtw uv.2.continuous ho F a c N,
    ∀(ε:ℕ → ℝ),MaximumDiagonal J ε J.OuterSampleGood →
    Tendsto ε atTop (𝓝 0) → ∀(q:Model n) (β:ℝ),riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) →
    ∀(r:Fin (Module.finrank ℝ (Model n)+1) → Model n)
      (m:Fin (Module.finrank ℝ (Model n)+1) → ℝ)
      (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r) →
    Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∀i,(show TangentSpace 𝓘(ℝ,Model n) a from r i)∈minimizingVectors a →
    0 < m i → ∀l κ:ℝ,
    deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=l →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=κ →
    1 < l → κ < 0 →
    (∀d,d≠0 → 0 < m i*L d d-(κ/l^2)*
        (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i) d)^2) →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
      (∀d,m i*L d d-(κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i) d)^2 ≤ V d d) ∧
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (l⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator V).det ≤
        (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*
          (expJacobian (n:=n) a (r i))^2 := by
  sorry
end MaximumTrueOuter
end WeakMTWTransport

end
end

end OAI
end
