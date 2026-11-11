-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_HodgeSmoothingCover_pairingGammaTail_integral
-- name    : OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingGammaTail_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:59.116199+00:00
-- url     : https://prove2.me/theorems/c2777a8e-64b2-4d0a-8304-05acd3564f97
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingGammaTail_integral: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingGammaTail_integral` of [lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgePairingHeat.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgePairingHeat.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover`, with `open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma pairingGammaTail_integral (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (hr : 0 < r)
--       (hρT : 2*ρ^2 ≤ T) (a b : PreL2 A J α hs ht true) :
--       (∫ x, ∫ y, C.pairingGammaTail T hT r a b x y
--         ∂geometricVolume A J α ∂geometricVolume A J α) =
--         ⟪hodgeGammaTailAction A J α hs ht D hD T r (smoothL2 A J α hs ht true a),
--           smoothL2 A J α hs ht true b⟫
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.geometricVolume` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingGammaTail` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeGammaTailAction` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_kernel` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgePairingHeat.lean (declaration OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingGammaTail_integral)

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

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {ρ : ℝ} {hρ : 0 < ρ} (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)

lemma pairingGammaTail_integral (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (hr : 0 < r)
    (hρT : 2*ρ^2 ≤ T) (a b : PreL2 A J α hs ht true) :
    (∫ x, ∫ y, C.pairingGammaTail T hT r a b x y
      ∂geometricVolume A J α ∂geometricVolume A J α) =
      ⟪hodgeGammaTailAction A J α hs ht D hD T r (smoothL2 A J α hs ht true a),
        smoothL2 A J α hs ht true b⟫ := by
  sorry

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end
