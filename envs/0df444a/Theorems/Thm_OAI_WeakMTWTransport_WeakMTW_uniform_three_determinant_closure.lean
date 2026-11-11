-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_uniform_three_determinant_closure
-- name    : OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:00:07.610744+00:00
-- url     : https://prove2.me/theorems/0e15c561-f92a-485a-8fba-1207e8518380
-- title:
--   OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure` of [lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ThreeDeterminantsClose.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ThreeDeterminantsClose.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle ContinuousLinearMap`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma WeakMTW.uniform_three_determinant_closure
--       (hmtw : WeakMTW (n := n) (M := M)) {μ κ A c₀ c₁ C₀ : ℝ}
--       (hμ : 0<μ) (hκ : 0<κ) (hA : 0<A) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hC₀ : 0<C₀) :
--       ∃ B : ℝ, 0<B ∧ ∀ (ι : Type) [Fintype ι] (x : M)
--         (v : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
--         (p : TangentSpace 𝓘(ℝ,Model n) x),
--         (∀ j,0 ≤ w j) → (∑ j,w j=1) → (∀ j,v j∈minimizingVectors x) →
--         p=∑ j,w j • v j → ∀ (i : ι) (e : TangentSpace 𝓘(ℝ,Model n) x) (t D : ℝ),
--         μ ≤ w i → ‖e‖=1 → 0<t → 0<D → 0 < inner ℝ p e →
--         κ*D ≤ (inner ℝ p e)^2 → ‖v i‖^2-‖p‖^2 ≤ A*D → v i=p+t • e →
--         ∀ l∈Icc (1/2:ℝ) 1, ∀ li∈Icc (1:ℝ) 2,
--         let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
--         let zi : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,v i⟩
--         let σ := expJacobian x p
--         let σi := expJacobian x (v i)
--         let σt := expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2)
--         let σti := expJacobian (reverseRay zi).1 (li⁻¹ • (reverseRay zi).2)
--         l⁻¹ • (reverseRay z).2∈minimizingVectors (reverseRay z).1 →
--         0<σ → 0<σi → 0<σt → 0<σti → ∀ V W K : ℝ, 0<K →
--         c₀*σ^2/σt ≤ V → W ≤ C₀*σi^2/σti → c₁*K*V ≤ W → K ≤ B
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.minimizingVectors` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.expJacobian` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.reverseRay` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.WeakMTW` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ThreeDeterminantsClose.lean (declaration OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure)

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
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport

section DeterminantClosure
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance threeDeterminantsCloseFiniteDimensionalTangentSpace_rdbee3f_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma WeakMTW.uniform_three_determinant_closure
    (hmtw : WeakMTW (n := n) (M := M)) {μ κ A c₀ c₁ C₀ : ℝ}
    (hμ : 0<μ) (hκ : 0<κ) (hA : 0<A) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hC₀ : 0<C₀) :
    ∃ B : ℝ, 0<B ∧ ∀ (ι : Type) [Fintype ι] (x : M)
      (v : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
      (p : TangentSpace 𝓘(ℝ,Model n) x),
      (∀ j,0 ≤ w j) → (∑ j,w j=1) → (∀ j,v j∈minimizingVectors x) →
      p=∑ j,w j • v j → ∀ (i : ι) (e : TangentSpace 𝓘(ℝ,Model n) x) (t D : ℝ),
      μ ≤ w i → ‖e‖=1 → 0<t → 0<D → 0 < inner ℝ p e →
      κ*D ≤ (inner ℝ p e)^2 → ‖v i‖^2-‖p‖^2 ≤ A*D → v i=p+t • e →
      ∀ l∈Icc (1/2:ℝ) 1, ∀ li∈Icc (1:ℝ) 2,
      let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
      let zi : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,v i⟩
      let σ := expJacobian x p
      let σi := expJacobian x (v i)
      let σt := expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2)
      let σti := expJacobian (reverseRay zi).1 (li⁻¹ • (reverseRay zi).2)
      l⁻¹ • (reverseRay z).2∈minimizingVectors (reverseRay z).1 →
      0<σ → 0<σi → 0<σt → 0<σti → ∀ V W K : ℝ, 0<K →
      c₀*σ^2/σt ≤ V → W ≤ C₀*σi^2/σti → c₁*K*V ≤ W → K ≤ B := by
  sorry
end DeterminantClosure
end WeakMTWTransport

end

end

end

end OAI
end
