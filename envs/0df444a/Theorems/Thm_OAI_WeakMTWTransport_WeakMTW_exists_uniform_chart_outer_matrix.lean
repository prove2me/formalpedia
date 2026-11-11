-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_uniform_chart_outer_matrix
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:01:48.098434+00:00
-- url     : https://prove2.me/theorems/795f3d84-8b65-47fa-90e4-be7f6cb562a6
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix` of [lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ChartOuterMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ChartOuterMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_uniform_chart_outer_matrix
--       (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
--       ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
--         uv∈densityDualClass (metricVolume n) lam cap x0 → Continuous φ → StrictMono φ →
--         ∀ (a:M) (b p:Model n),b∈(extChartAt 𝓘(ℝ,Model n) a).target →
--         let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,chartFiberInverse a b p⟩
--         ∀ l:ℝ,z.2∈activeLogs (φ ∘ uv.2) z.1 →
--         ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)) →
--         HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2)) → 1 < l →
--         iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0 →
--         ∀ B:Model n →L[ℝ] Model n →L[ℝ] ℝ,
--         (∀d e,B d e=B e d) → (∀d,0 ≤ B d d) →
--         HasLowerSecondTaylor (fun d=>φ (uv.2 (movingNormal a (b,p+d)))+
--           ‖chartFiberInverse a b (p+d)‖^2/2) 0 B →
--         ∃V:Model n →L[ℝ] Model n,
--           (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
--           (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
--           (∀d,B d d-(iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2))/l^2)*
--             (frameMetric a b p d)^2 ≤ inner ℝ (V d) d) ∧
--           0 < expJacobian (n:=n) z.1 z.2 ∧
--           0 < expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2) ∧
--           expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2)*V.det ≤
--             (chartFiberInverse a b).toLinearMap.normDet^2*l^n*K*(expJacobian (n:=n) z.1 z.2)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor`, `OAI.WeakMTWTransport.activeLogs`, `OAI.WeakMTWTransport.chartFiberInverse` and `OAI.WeakMTWTransport.movingNormal` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.expJacobian` and `OAI.WeakMTWTransport.frameMetric` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.densityDualClass` and `OAI.WeakMTWTransport.reverseRay` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ChartOuterMatrix.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix)

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
section ChartOuterMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance chartOuterFinite_r3c95b1_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance chartOuterComplete_r3c95b1_1 (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
lemma WeakMTW.exists_uniform_chart_outer_matrix
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → Continuous φ → StrictMono φ →
      ∀ (a:M) (b p:Model n),b∈(extChartAt 𝓘(ℝ,Model n) a).target →
      let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,chartFiberInverse a b p⟩
      ∀ l:ℝ,z.2∈activeLogs (φ ∘ uv.2) z.1 →
      ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)) →
      HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2)) → 1 < l →
      iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0 →
      ∀ B:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,B d e=B e d) → (∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (movingNormal a (b,p+d)))+
        ‖chartFiberInverse a b (p+d)‖^2/2) 0 B →
      ∃V:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,B d d-(iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2))/l^2)*
          (frameMetric a b p d)^2 ≤ inner ℝ (V d) d) ∧
        0 < expJacobian (n:=n) z.1 z.2 ∧
        0 < expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2) ∧
        expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2)*V.det ≤
          (chartFiberInverse a b).toLinearMap.normDet^2*l^n*K*(expJacobian (n:=n) z.1 z.2)^2 := by
  sorry
end ChartOuterMatrix
end WeakMTWTransport

end
end

end OAI
end
