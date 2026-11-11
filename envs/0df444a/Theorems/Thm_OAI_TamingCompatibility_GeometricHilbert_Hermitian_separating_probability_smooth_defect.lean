-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_separating_probability_smooth_defect
-- name    : OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_smooth_defect
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:36:21.604217+00:00
-- url     : https://prove2.me/theorems/8ea23e2d-556d-48fe-817b-a205c8331810
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_smooth_defect: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_smooth_defect` of [lean/OAI/Geometry/TamingCompatibility/Concentration/RadialDefectCombination.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/RadialDefectCombination.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.Hermitian`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter _root_.MeasureTheory RadialPotential`, `open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace`):
--
--   ```lean
--   theorem separating_probability_smooth_defect
--       (hR1 : 2*R ≤ 1)
--       (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
--       (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
--       ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r ≤ R ∧
--         ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ K₀,
--           ∫ u, smoothUnitDefect J α hs ht p.val b r s u ∂μ ≤ C
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable`, `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.chartDensity` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.hermitianMetric` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.Hermitian.smoothUnitDefect` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy`, `OAI.TamingCompatibility.GeometricHilbert.antiToEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti` and `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete` (definitions bundle `OAIQ239Tc034` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsInvariant`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.separating_probability_atlas_defect` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/RadialDefectCombination.lean (declaration OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_smooth_defect)

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

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel

variable (A : FiniteCharts X)
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
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hH hweak hB hdual hU hUD hτ hρ hφ hc hφD hK hKU hφone hR hK₀ hcenters in

theorem separating_probability_smooth_defect
    (hR1 : 2*R ≤ 1)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r ≤ R ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ K₀,
        ∫ u, smoothUnitDefect J α hs ht p.val b r s u ∂μ ≤ C := by
  sorry

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end
