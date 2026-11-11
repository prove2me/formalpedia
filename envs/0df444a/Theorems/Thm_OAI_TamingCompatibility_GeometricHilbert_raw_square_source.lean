-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_raw_square_source
-- name    : OAI.TamingCompatibility.GeometricHilbert.raw_square_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:31:18.604753+00:00
-- url     : https://prove2.me/theorems/7c7f58a8-5cc6-4ba9-b19f-fdfecf903018
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.raw_square_source: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.raw_square_source` of [lean/OAI/Geometry/TamingCompatibility/Functional/WeakNormal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Functional/WeakNormal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution`, `open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace`):
--
--   ```lean
--   lemma raw_square_source (p : A.centers) (τ : 𝓢(Space,ℝ))
--       {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
--       (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
--       (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
--       (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ))
--       (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p) i z)
--       (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p) z)
--       (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
--       (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
--       (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
--         ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫)
--       (g : 𝓢(Space,EuclideanEnergy.Pair))
--       (hg : ∀ z ∈ U, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
--       (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχU : tsupport χ ⊆ U) :
--       smulLeftCLM (C 2) χ (ComplexMatrix.square EuclideanEnergy.e a b ρ
--         (rawDistribution A J α hs ht D hD p τ u)) =
--       smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ComplexMatrix.C`, `OAI.TamingCompatibility.ComplexMatrix.R`, `OAI.TamingCompatibility.ComplexMatrix.embed`, `OAI.TamingCompatibility.ComplexMatrix.square`, `OAI.TamingCompatibility.EuclideanEnergy.V` and `OAI.TamingCompatibility.EuclideanEnergy.e` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.EuclideanEnergy.Pair`, `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts`, `OAI.TamingCompatibility.ManifoldVolume.chartDensity` and `OAI.TamingCompatibility.ScalarPair.F` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.GeometricChart.normalA`, `OAI.TamingCompatibility.GeometricChart.normalB`, `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricChart.rawPair` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.GeometricHilbert.rawDistribution` (definitions bundle `OAIQ239Tc029` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source`, `OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source_on`, `OAI.TamingCompatibility.GeometricHilbert.raw_smooth_near` and `OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Functional/WeakNormal.lean (declaration OAI.TamingCompatibility.GeometricHilbert.raw_square_source)

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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma raw_square_source (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p) i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p) z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫)
    (g : 𝓢(Space,EuclideanEnergy.Pair))
    (hg : ∀ z ∈ U, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχU : tsupport χ ⊆ U) :
    smulLeftCLM (C 2) χ (ComplexMatrix.square EuclideanEnergy.e a b ρ
      (rawDistribution A J α hs ht D hD p τ u)) =
    smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
  sorry

end TamingCompatibility.GeometricHilbert

end

end OAI
end
