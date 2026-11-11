-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_raw_two_jet_estimate
-- name    : OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:32:16.209531+00:00
-- url     : https://prove2.me/theorems/2b87fd3b-120d-4939-a20b-ac3bea27ea80
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RawJetEstimate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RawJetEstimate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators`, `open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv`):
--
--   ```lean
--   lemma raw_two_jet_estimate (p : A.centers) (τ : 𝓢(Space,ℝ))
--       {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
--       (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
--       (q : Space) (hq : q ∈ U) :
--       ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
--         ∀ (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
--         ∃ K : ℝ, 0 ≤ K ∧ ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)),
--           (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
--           (∀ v : antiEnergy A J α hs ht,
--             ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
--               ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
--           ∀ x : Space, coordinateTwoJet (localizedRawSchwartz A J α hs ht D hD p τ χ a) x ≤
--             K * (‖antiToEnergy A J α hs ht a‖ +
--               ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ComplexMatrix.C`, `OAI.TamingCompatibility.ComplexMatrix.R`, `OAI.TamingCompatibility.ComplexMatrix.embed` and `OAI.TamingCompatibility.HilbertSobolev.H` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.EuclideanEnergy.Pair`, `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.chartDensity` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.HilbertSobolev.schwartzToH` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricChart.rawPair` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.coordinateTwoJet` (definitions bundle `OAIQ239Tc019` of this split); `OAI.TamingCompatibility.GeometricHilbert.localizedRawSchwartz` (definitions bundle `OAIQ239Tc024` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy`, `OAI.TamingCompatibility.GeometricHilbert.antiToEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.exists_local_ddstar_estimate_on` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/RawJetEstimate.lean (declaration OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028

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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma raw_two_jet_estimate (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∀ (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)),
        (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
        (∀ v : antiEnergy A J α hs ht,
          ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
            ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ∀ x : Space, coordinateTwoJet (localizedRawSchwartz A J α hs ht D hD p τ χ a) x ≤
          K * (‖antiToEnergy A J α hs ht a‖ +
            ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖) := by
  sorry

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end
