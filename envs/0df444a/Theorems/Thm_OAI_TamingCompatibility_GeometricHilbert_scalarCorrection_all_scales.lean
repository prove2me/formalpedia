-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_scalarCorrection_all_scales
-- name    : OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:37:25.438862+00:00
-- url     : https://prove2.me/theorems/7dc667e4-b672-45e0-9cc2-343ce337b0b1
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RadialFixedJet.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RadialFixedJet.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators`, `open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace`):
--
--   ```lean
--   theorem scalarCorrection_all_scales
--       (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
--       (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
--       (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
--       (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
--       (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
--       (q : Space) (hq : q ∈ U) :
--       ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
--         ∀ y ∈ Metric.ball q δ,
--         (∀ r > (0:ℝ), ∀ (φ : supportedSchwartz K) (j : Fin 2) (b : Space) (M : ℝ),
--           0 ≤ M → tsupport φ.val ⊆ Metric.ball b r → (∀ z, |φ.val z| ≤ M) →
--           (∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ρ z * φ.val z) z‖ ≤ M/r^k) →
--           ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M) ∧
--         (∀ r ∈ Ioo (0:ℝ) δ, ∀ (φ : supportedSchwartz K) (j : Fin 2) (b : Space) (R M : ℝ),
--           0 ≤ R → 0 ≤ M → tsupport φ.val ⊆ Metric.ball b R → (∀ z, |φ.val z| ≤ M) →
--           R+c*r ≤ dist b y →
--           ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M*R^3/r^3)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricForms.Form` (definitions bundle `OAIQ239Tc000` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.chartDensity` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.supportedSchwartz` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.GeometricChart.Data` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy`, `OAI.TamingCompatibility.GeometricHilbert.antiToEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.scalarCorrectionLM` (definitions bundle `OAIQ239Tc027` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti` and `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete` (definitions bundle `OAIQ239Tc034` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_logSource_compact` and `OAI.TamingCompatibility.GeometricHilbert.Hermitian.nonharmonic_sqrtSource_compact` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RadialFixedJet.lean (declaration OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales)

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

theorem scalarCorrection_all_scales
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ,
      (∀ r > (0:ℝ), ∀ (φ : supportedSchwartz K) (j : Fin 2) (b : Space) (M : ℝ),
        0 ≤ M → tsupport φ.val ⊆ Metric.ball b r → (∀ z, |φ.val z| ≤ M) →
        (∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ρ z * φ.val z) z‖ ≤ M/r^k) →
        ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M) ∧
      (∀ r ∈ Ioo (0:ℝ) δ, ∀ (φ : supportedSchwartz K) (j : Fin 2) (b : Space) (R M : ℝ),
        0 ≤ R → 0 ≤ M → tsupport φ.val ⊆ Metric.ball b R → (∀ z, |φ.val z| ≤ M) →
        R+c*r ≤ dist b y →
        ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M*R^3/r^3) := by
  sorry

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end
