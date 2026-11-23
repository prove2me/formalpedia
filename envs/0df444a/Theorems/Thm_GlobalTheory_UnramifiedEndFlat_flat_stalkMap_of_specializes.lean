-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_stalkMap_of_specializes
-- name    : GlobalTheory.UnramifiedEndFlat.flat_stalkMap_of_specializes
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:21.866821+00:00
-- url     : https://prove2.me/theorems/cc59c4bb-47fe-440e-8531-15c8b55719e0
-- title:
--   Unramified End Flat: flat stalk Map of specializes
-- statement:
--   The Unramified End Flat construction uses the flat stalk Map of specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L79-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
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
open GlobalTheory.UnramifiedEndFlat
open IsLocalRing

theorem GlobalTheory.UnramifiedEndFlat.flat_stalkMap_of_specializes {X Y : Scheme.{0}} (f : X ⟶ Y) {x x' : X} (h : x ⤳ x')
    (hf : (f.stalkMap x').hom.Flat) : (f.stalkMap x).hom.Flat := by sorry
