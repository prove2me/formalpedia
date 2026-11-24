-- Prove2me | Theorems.Thm_GlobalTheory_T_map_comap_eq_comap_map_of_flat
-- name    : GlobalTheory.T.map_comap_eq_comap_map_of_flat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:59.220969+00:00
-- url     : https://prove2.me/theorems/0be885e5-a0a0-4deb-a530-45324aede928
-- title:
--   T: map comap eq comap map of flat
-- statement:
--   The T construction uses the map comap eq comap map of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapFlatStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapFlatStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapFlat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapFlatStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.map_comap_eq_comap_map_of_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W') (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π → ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by sorry
