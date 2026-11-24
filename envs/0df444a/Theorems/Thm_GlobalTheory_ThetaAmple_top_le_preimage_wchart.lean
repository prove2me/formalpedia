-- Prove2me | Theorems.Thm_GlobalTheory_ThetaAmple_top_le_preimage_wchart
-- name    : GlobalTheory.ThetaAmple.top_le_preimage_wchart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:42.956815+00:00
-- url     : https://prove2.me/theorems/b2488249-32c6-4e00-84a0-d9e31a644b4d
-- title:
--   Theta Ample: top le preimage wchart
-- statement:
--   The Theta Ample construction uses the top le preimage wchart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L30-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple

theorem GlobalTheory.ThetaAmple.top_le_preimage_wchart {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) {N : ℕ} (j : Fin N → L.ι) (x : Sp ℂ ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ (LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).U j ↔ ∀ k, ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j k) := by sorry
