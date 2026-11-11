-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_exists_local_ddstar_estimate_on
-- name    : OAI.TamingCompatibility.GeometricHilbert.exists_local_ddstar_estimate_on
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:30:11.615676+00:00
-- url     : https://prove2.me/theorems/a6293212-d144-466c-b436-3edf5106adea
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.exists_local_ddstar_estimate_on: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.exists_local_ddstar_estimate_on` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAntiRHSBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAntiRHSBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint`, `open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators`, `open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace`):
--
--   ```lean
--   lemma exists_local_ddstar_estimate_on (p : A.centers) (τ : 𝓢(Space,ℝ))
--       (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
--       (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
--       (q : Space) (hqU : q ∈ U) :
--       ∃ ρ : 𝓢(Space,ℝ), HasCompactSupport (ρ : Space → ℝ) ∧ tsupport ρ ⊆ U ∧
--       ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ (D p).domain ∧
--         ∃ C : ℝ, 0 ≤ C ∧ ∀ (f a : antiPre A J α hs ht),
--           (∀ v : antiEnergy A J α hs ht,
--             ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
--               ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
--           ∀ x ∈ O,
--             ‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a.val.val))
--               (extChartAt Model p.val).symm x‖ ≤
--               C * (‖antiToEnergy A J α hs ht a‖ +
--                 ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
--                   (weightedRawRHS A J α hs ht D hD p τ ρ f))‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ComplexMatrix.C`, `OAI.TamingCompatibility.ComplexMatrix.R`, `OAI.TamingCompatibility.ComplexMatrix.embed` and `OAI.TamingCompatibility.HilbertSobolev.H` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model`, `OAI.TamingCompatibility.ManifoldForms.Space`, `OAI.TamingCompatibility.ManifoldForms.exteriorDerivative` and `OAI.TamingCompatibility.ManifoldForms.pullback` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldHodge.codifferential` (definitions bundle `OAIQ239Tc006` of this split); `OAI.TamingCompatibility.HilbertSobolev.schwartzToH` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.weightedRawRHS` (definitions bundle `OAIQ239Tc024` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy`, `OAI.TamingCompatibility.GeometricHilbert.antiToEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAntiRHSBound.lean (declaration OAI.TamingCompatibility.GeometricHilbert.exists_local_ddstar_estimate_on)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028

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
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma exists_local_ddstar_estimate_on (p : A.centers) (τ : 𝓢(Space,ℝ))
    (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hqU : q ∈ U) :
    ∃ ρ : 𝓢(Space,ℝ), HasCompactSupport (ρ : Space → ℝ) ∧ tsupport ρ ⊆ U ∧
    ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ (D p).domain ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (f a : antiPre A J α hs ht),
        (∀ v : antiEnergy A J α hs ht,
          ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
            ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ∀ x ∈ O,
          ‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a.val.val))
            (extChartAt Model p.val).symm x‖ ≤
            C * (‖antiToEnergy A J α hs ht a‖ +
              ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
                (weightedRawRHS A J α hs ht D hD p τ ρ f))‖) := by
  sorry

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end
