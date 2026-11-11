-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_closedLift_scalar_off_source
-- name    : OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:36:57.06768+00:00
-- url     : https://prove2.me/theorems/ba885ca3-8743-4d87-9ee4-3da0415e42ab
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RadialScalarOff.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RadialScalarOff.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators`, `open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace`):
--
--   ```lean
--   theorem closedLift_scalar_off_source
--       (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
--       (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
--       (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
--       (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
--       (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
--       (q : Space) (hq : q ∈ U)
--       (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
--       (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
--       (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
--       (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
--       (hχ0 : ((χ 4 : Space → ℂ) =ᶠ[𝓝 0] fun _ => 1)) :
--       ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q),
--         ∀ (_hr : 0 < t.1), t.1 ≤ 1 →
--         ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
--           (hφK : tsupport φ ⊆ K) (j : Fin 2) (b : Space) (R M : ℝ), 0 ≤ R → 0 ≤ M →
--           tsupport φ ⊆ Metric.ball b R → (∀ z, |φ z| ≤ M) →
--           R+c*t.1 ≤ dist b t.2 →
--           let f := testAnti A J α hs ht D p (componentTest j φ)
--             (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
--           ‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
--             (extChartAt Model p.val).symm t.2 -
--             ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm t.2‖ ≤ C*M*R^3/t.1^3
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ComplexMatrix.R` and `OAI.TamingCompatibility.ComplexMatrix.componentTest` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model`, `OAI.TamingCompatibility.ManifoldForms.Space` and `OAI.TamingCompatibility.ManifoldForms.pullback` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.chartDensity` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.componentTest_compact` and `OAI.TamingCompatibility.GeometricHilbert.componentTest_support` (definitions bundle `OAIQ239Tc019` of this split); `OAI.TamingCompatibility.GeometricHilbert.closedLiftOfInverse` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.GeometricHilbert.testAnti` (definitions bundle `OAIQ239Tc024` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy`, `OAI.TamingCompatibility.GeometricHilbert.antiToEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti` and `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete` (definitions bundle `OAIQ239Tc034` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_local_estimates` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RadialScalarOff.lean (declaration OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034

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

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem closedLift_scalar_off_source
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    (hχ0 : ((χ 4 : Space → ℂ) =ᶠ[𝓝 0] fun _ => 1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q),
      ∀ (_hr : 0 < t.1), t.1 ≤ 1 →
      ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
        (hφK : tsupport φ ⊆ K) (j : Fin 2) (b : Space) (R M : ℝ), 0 ≤ R → 0 ≤ M →
        tsupport φ ⊆ Metric.ball b R → (∀ z, |φ z| ≤ M) →
        R+c*t.1 ≤ dist b t.2 →
        let f := testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
        ‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
          (extChartAt Model p.val).symm t.2 -
          ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm t.2‖ ≤ C*M*R^3/t.1^3 := by
  sorry

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end
