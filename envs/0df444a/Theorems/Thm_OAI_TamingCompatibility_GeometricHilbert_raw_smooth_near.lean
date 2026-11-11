-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_raw_smooth_near
-- name    : OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:35.06002+00:00
-- url     : https://prove2.me/theorems/06f1b80c-6cbf-4b46-bd47-e6bfe0812eb8
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RawRepresentative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RawRepresentative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart`, `open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev`, `open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction`):
--
--   ```lean
--   lemma raw_smooth_near (p : A.centers) (q : Space) (hq : q ∈ (D p).domain)
--       (hwq : coordinateWeight A p q ≠ 0)
--       (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
--       (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
--         ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
--       ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
--         (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
--         ∃ g : Space →ᵇ ScalarPair.F, ContDiff ℝ ∞ (g : Space → ScalarPair.F) ∧
--         ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
--           rawDistribution A J α hs ht D hD p τ u χ = EuclideanSobolev.boundedDistribution g χ
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.EuclideanSobolev.boundedDistribution` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ScalarPair.F` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.GeometricHilbert.rawDistribution` (definitions bundle `OAIQ239Tc029` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_smooth_defect`, `OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound`, `OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse`, `OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound`, `OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate`, `OAI.TamingCompatibility.separating_probability_atlas_defect` and `OAI.TamingCompatibility.separating_probability_local_quadratic` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RawRepresentative.lean (declaration OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028
import Definitions.Def_OAIQ239Tc029

section

attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma raw_smooth_near (p : A.centers) (q : Space) (hq : q ∈ (D p).domain)
    (hwq : coordinateWeight A p q ≠ 0)
    (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
      (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
      ∃ g : Space →ᵇ ScalarPair.F, ContDiff ℝ ∞ (g : Space → ScalarPair.F) ∧
      ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
        rawDistribution A J α hs ht D hD p τ u χ = EuclideanSobolev.boundedDistribution g χ := by
  sorry

end TamingCompatibility.GeometricHilbert

end

end OAI
end
