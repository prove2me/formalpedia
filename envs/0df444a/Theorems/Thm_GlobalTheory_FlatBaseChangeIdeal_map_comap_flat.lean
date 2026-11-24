-- Prove2me | Theorems.Thm_GlobalTheory_FlatBaseChangeIdeal_map_comap_flat
-- name    : GlobalTheory.FlatBaseChangeIdeal.map_comap_flat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:31:21.813799+00:00
-- url     : https://prove2.me/theorems/817fdb5b-b51e-45de-a85c-90ee73b0924a
-- title:
--   Flat Base Change Ideal: map comap flat
-- statement:
--   The Flat Base Change Ideal construction uses the map comap flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapFlat.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapFlat.lean#L46-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapFlat
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
open GlobalTheory GlobalTheory.FlatBaseChangeIdeal

theorem GlobalTheory.FlatBaseChangeIdeal.map_comap_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W')
    (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π →
    ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by sorry
