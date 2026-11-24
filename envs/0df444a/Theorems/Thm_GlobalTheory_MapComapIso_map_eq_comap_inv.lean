-- Prove2me | Theorems.Thm_GlobalTheory_MapComapIso_map_eq_comap_inv
-- name    : GlobalTheory.MapComapIso.map_eq_comap_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:20:09.887097+00:00
-- url     : https://prove2.me/theorems/348d9b2c-acdd-4e24-aa2a-543bf1c36278
-- title:
--   Map Comap Iso: map eq comap inv
-- statement:
--   The Map Comap Iso construction uses the map eq comap inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapIdealSheafEqOfIsIsoRestrict.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapIdealSheafEqOfIsIsoRestrict.lean#L10-L20

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

theorem GlobalTheory.MapComapIso.map_eq_comap_inv {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (K : X.IdealSheafData) :
    K.map f = K.comap (inv f) := by sorry
