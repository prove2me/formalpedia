-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_closedLift_scaled_basis_local_bound
-- name    : OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:06.939482+00:00
-- url     : https://prove2.me/theorems/240e78cf-2f97-426a-b340-2493c7c68a13
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/ClosedLiftBasisBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/ClosedLiftBasisBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set ComplexMatrix`, `open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv`):
--
--   ```lean
--   lemma closedLift_scaled_basis_local_bound {ι : Type*} [Fintype ι]
--       (b : Module.Basis ι ℝ Space) (p : A.centers) (τ : 𝓢(Space,ℝ)) (η : 𝓢(Space,ℂ))
--       (L : Space ≃L[ℝ] Space) {U K : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
--       (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1) (hη : ∀ z ∈ U, η z = 1)
--       (hK : IsCompact K) (hKU : K ⊆ U) :
--       ∃ C₀ : ℝ, 0 ≤ C₀ ∧
--         ∀ (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
--           (f : antiPre A J α hs ht) (z : Space), z ∈ K →
--           ∀ (r M : ℝ), 0 < r → r ≤ 1 →
--         (let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
--             (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))
--          r*‖u (L z)‖ + r^2*∑ i, ‖(∂_{b i} u) (L z)‖ +
--            r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} u)) (L z)‖ ≤ M) →
--         r^3*‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
--           (extChartAt Model p.val).symm z -
--           ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm z‖ ≤ C₀*M
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ComplexMatrix.C` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model`, `OAI.TamingCompatibility.ManifoldForms.Space` and `OAI.TamingCompatibility.ManifoldForms.pullback` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add` and `OAI.TamingCompatibility.GeometricHilbert.preL2Module` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.closedLiftOfInverse` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.GeometricHilbert.localizedRawSchwartz` (definitions bundle `OAIQ239Tc024` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_logError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_sqrtError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source`, `OAI.TamingCompatibility.GeometricHilbert.correctedDdc_off_source_compact`, `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales` and `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_local_estimates` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/ClosedLiftBasisBound.lean (declaration OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc024

section

attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set ComplexMatrix
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in

lemma closedLift_scaled_basis_local_bound {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ Space) (p : A.centers) (τ : 𝓢(Space,ℝ)) (η : 𝓢(Space,ℂ))
    (L : Space ≃L[ℝ] Space) {U K : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1) (hη : ∀ z ∈ U, η z = 1)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
        (f : antiPre A J α hs ht) (z : Space), z ∈ K →
        ∀ (r M : ℝ), 0 < r → r ≤ 1 →
      (let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))
       r*‖u (L z)‖ + r^2*∑ i, ‖(∂_{b i} u) (L z)‖ +
         r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} u)) (L z)‖ ≤ M) →
      r^3*‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
        (extChartAt Model p.val).symm z -
        ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm z‖ ≤ C₀*M := by
  sorry

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end
