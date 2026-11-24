-- Prove2me | Theorems.Thm_GlobalTheory_PointsCompact_continuous_comp
-- name    : GlobalTheory.PointsCompact.continuous_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:51:16.302806+00:00
-- url     : https://prove2.me/theorems/91d80182-ec28-4148-a462-f88c74d9c961
-- title:
--   Points Compact: continuous comp
-- statement:
--   The Points Compact construction uses the continuous comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CompactSpacePointsPolAV.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CompactSpacePointsPolAV.lean#L122-L132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CompactSpacePointsPolAV
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
noncomputable section
open GlobalTheory GlobalTheory.PointsCompact

theorem GlobalTheory.PointsCompact.continuous_comp (h1 : ValueRules) {X Y : Over (Sp ℂ)} (φ : X ⟶ Y) :
    @Continuous _ _ (pointTopology X) (pointTopology Y) (fun x => x ≫ φ) := by sorry
