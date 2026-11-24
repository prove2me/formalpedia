-- Prove2me | Theorems.Thm_GlobalTheory_isMonHom_of_pullback_of_flat
-- name    : GlobalTheory.isMonHom_of_pullback_of_flat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:08.992201+00:00
-- url     : https://prove2.me/theorems/6b4f344e-83af-4b22-bf20-e0a9de219f93
-- title:
--   Global Theory: is Mon Hom of pullback of flat
-- statement:
--   The Global Theory construction uses the is Mon Hom of pullback of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L89-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L89-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
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
variable {S S' : Scheme.{0}} (f : S' ⟶ S) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]

theorem GlobalTheory.isMonHom_of_pullback_of_flat {G G' : Over S} [MonObj G] [MonObj G'] (F : G ⟶ G')
    [Flat G.hom] [IsSeparated G'.hom] [h : IsMonHom ((Over.pullback f).map F)] : IsMonHom F := by sorry
