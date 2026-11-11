-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodge_lift_local_estimate
-- name    : OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:37:13.513198+00:00
-- url     : https://prove2.me/theorems/baa268c6-749b-415b-a206-5a1a10278e39
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAntiNorms.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAntiNorms.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricChart`, `open ComplexMatrix TemperedDistribution HilbertSobolev Set`, `open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace`):
--
--   ```lean
--   lemma hodge_lift_local_estimate
--       (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
--       (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
--         (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
--       (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
--         weakDelta A J α hs ht v⟫ =
--         ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
--       (C₀ : ℝ) (hC₀ : 0 < C₀)
--       (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
--         (∀ v : antiEnergy A J α hs ht,
--           |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
--           ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C₀*M)
--       (p : A.centers) (q : Space) (hq : q ∈ (D p).domain)
--       (hwq : coordinateWeight A p q ≠ 0) :
--       ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ (D p).domain ∧
--         ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
--           ∀ (a : PreL2 A J α hs ht true) (x : Space), x ∈ O →
--             ‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht
--               (Gs (smoothAntiProjection A J α hs ht a)).val.val))
--               (extChartAt Model p.val).symm x‖ ≤
--                 C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model`, `OAI.TamingCompatibility.ManifoldForms.Space`, `OAI.TamingCompatibility.ManifoldForms.exteriorDerivative` and `OAI.TamingCompatibility.ManifoldForms.pullback` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldHodge.codifferential` (definitions bundle `OAIQ239Tc006` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms`, `OAI.TamingCompatibility.GeometricChart.Data` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.smoothAntiProjection` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeSmoothShift` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy`, `OAI.TamingCompatibility.GeometricHilbert.antiToEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti` and `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete` (definitions bundle `OAIQ239Tc034` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAntiNorms.lean (declaration OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034

section

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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricChart
open ComplexMatrix TemperedDistribution HilbertSobolev Set
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma hodge_lift_local_estimate
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
      (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
    (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
      weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
        ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C₀*M)
    (p : A.centers) (q : Space) (hq : q ∈ (D p).domain)
    (hwq : coordinateWeight A p q ≠ 0) :
    ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ (D p).domain ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
        ∀ (a : PreL2 A J α hs ht true) (x : Space), x ∈ O →
          ‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht
            (Gs (smoothAntiProjection A J α hs ht a)).val.val))
            (extChartAt Model p.val).symm x‖ ≤
              C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  sorry
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end
