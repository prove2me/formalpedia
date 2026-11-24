-- Prove2me | Theorems.Thm_GlobalTheory_isSchemeTheoreticallyDominant_toImage
-- name    : GlobalTheory.isSchemeTheoreticallyDominant_toImage
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:11.361247+00:00
-- url     : https://prove2.me/theorems/645d4379-0ce6-493c-bca7-e21781ca3fb5
-- title:
--   Global Theory: is Scheme Theoretically Dominant to Image
-- statement:
--   The Global Theory construction uses the is Scheme Theoretically Dominant to Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfIsSchemeTheoreticallyDominantOfFractionRing.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfIsSchemeTheoreticallyDominantOfFractionRing.lean#L22-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfIsSchemeTheoreticallyDominantOfFractionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by sorry
