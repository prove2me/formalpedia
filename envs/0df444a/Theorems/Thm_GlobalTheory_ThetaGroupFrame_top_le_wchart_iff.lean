-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_wchart_iff
-- name    : GlobalTheory.ThetaGroupFrame.top_le_wchart_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:44.928677+00:00
-- url     : https://prove2.me/theorems/c4b91f0a-eb72-45df-a520-f502dd6942d1
-- title:
--   Theta Group Frame: top le wchart iff
-- statement:
--   The Theta Group Frame construction uses the top le wchart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L41-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame

theorem GlobalTheory.ThetaGroupFrame.top_le_wchart_iff {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (j : K → L.ι) (x : Z ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by sorry
