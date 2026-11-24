-- Prove2me | Theorems.Thm_GlobalTheory_OriginFrame_rigChart_iff
-- name    : GlobalTheory.OriginFrame.rigChart_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:23.028805+00:00
-- url     : https://prove2.me/theorems/36b4575a-c904-40f4-aecb-4ccab45b9556
-- title:
--   Origin Frame: rig Chart iff
-- statement:
--   The Origin Frame construction uses the rig Chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsAppellHumbertFrameIsRig.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsAppellHumbertFrameIsRig.lean#L24-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsAppellHumbertFrameIsRig
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
open GlobalTheory
open GlobalTheory.OriginFrame

theorem GlobalTheory.OriginFrame.rigChart_iff {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X) (j : (L.pull x).ι) :
    ⊤ ≤ (L.pull x).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by sorry
