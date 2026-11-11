-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_uniform_outer_normal_det_bound_second
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:59:12.081197+00:00
-- url     : https://prove2.me/theorems/66f68398-ff12-4fb9-a03e-e127522cdcdc
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second` of [lean/OAI/Analysis/BiholderTransport/Regularity/OuterIntrinsicSecond.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/OuterIntrinsicSecond.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_uniform_outer_normal_det_bound_second
--       (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0<lam) (hcap:0 ≤ cap) :
--       ∃K:ℝ,0<K ∧ ∀ (a:M) (r:TangentSpace 𝓘(ℝ,Model n) a) (G:M×M → ℝ) (l:ℝ),
--         r∈minimizingVectors a →
--         ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
--           (a,riemannianExp a r) →
--         (∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),z.2∈injectivityDomain z.1 →
--           (fun q:M×M=>cost q.1 q.2)=ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) → 1<l →
--         ∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
--         uv∈densityDualClass (metricVolume n) lam cap x0 → StrictMono φ →
--         ContDiffAt ℝ 2 φ (uv.2 a) → HasDerivAt φ l (uv.2 a) → iteratedDeriv 2 φ (uv.2 a)≤0 →
--         ∀H:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] ℝ,
--         (∀d e,H d e=H e d) → (∀d,0≤H d d) →
--         HasLowerSecondTaylor (fun w=>φ (uv.2 (riemannianExp a w))+
--           G (riemannianExp a w,riemannianExp a r)) 0 H →
--         ∃V:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a,
--           (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
--           (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
--           (∀d,inner ℝ (V d) d=H d d+
--             (l*hessianValue a (l⁻¹ • r) d-
--               fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp a w,riemannianExp a r))) 0 d d)-
--             (iteratedDeriv 2 φ (uv.2 a)/l^2)*(inner ℝ r d)^2) ∧
--           expJacobian (n:=n) a (l⁻¹ • r)*V.det≤l^n*K
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor` and `OAI.WeakMTWTransport.minimizingVectors` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.hessianValue` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.expJacobian` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.cost`, `OAI.WeakMTWTransport.injectivityDomain`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_true_matrix` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/OuterIntrinsicSecond.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second)

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
section OuterIntrinsicSecond
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance oisFinite_rbd863c_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma WeakMTW.exists_uniform_outer_normal_det_bound_second
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0<lam) (hcap:0 ≤ cap) :
    ∃K:ℝ,0<K ∧ ∀ (a:M) (r:TangentSpace 𝓘(ℝ,Model n) a) (G:M×M → ℝ) (l:ℝ),
      r∈minimizingVectors a →
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (a,riemannianExp a r) →
      (∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),z.2∈injectivityDomain z.1 →
        (fun q:M×M=>cost q.1 q.2)=ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) → 1<l →
      ∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.2 a) → HasDerivAt φ l (uv.2 a) → iteratedDeriv 2 φ (uv.2 a)≤0 →
      ∀H:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] ℝ,
      (∀d e,H d e=H e d) → (∀d,0≤H d d) →
      HasLowerSecondTaylor (fun w=>φ (uv.2 (riemannianExp a w))+
        G (riemannianExp a w,riemannianExp a r)) 0 H →
      ∃V:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,inner ℝ (V d) d=H d d+
          (l*hessianValue a (l⁻¹ • r) d-
            fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp a w,riemannianExp a r))) 0 d d)-
          (iteratedDeriv 2 φ (uv.2 a)/l^2)*(inner ℝ r d)^2) ∧
        expJacobian (n:=n) a (l⁻¹ • r)*V.det≤l^n*K := by
  sorry
end OuterIntrinsicSecond
end WeakMTWTransport

end
end

end OAI
end
