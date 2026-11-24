-- Prove2me | Theorems.Thm_GlobalTheory_MapComapIso_map_comap_of_isIso
-- name    : GlobalTheory.MapComapIso.map_comap_of_isIso
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:35.09679+00:00
-- url     : https://prove2.me/theorems/8033f916-89cb-4302-a316-b5b670c50841
-- title:
--   Map Comap Iso: map comap of is Iso
-- statement:
--   The Map Comap Iso construction uses the map comap of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapIdealSheafEqOfIsIsoRestrict.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapIdealSheafEqOfIsIsoRestrict.lean#L22-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapFlatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory GlobalTheory.MapComapIso

theorem GlobalTheory.MapComapIso.map_comap_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (I : Y.IdealSheafData) :
    (I.comap f).map f = I := by sorry
