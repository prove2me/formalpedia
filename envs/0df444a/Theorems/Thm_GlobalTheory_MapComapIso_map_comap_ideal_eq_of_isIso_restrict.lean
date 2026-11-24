-- Prove2me | Theorems.Thm_GlobalTheory_MapComapIso_map_comap_ideal_eq_of_isIso_restrict
-- name    : GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:20:19.907529+00:00
-- url     : https://prove2.me/theorems/40c8a548-837d-4773-961f-8990c3aa32fc
-- title:
--   Map Comap Iso: map comap ideal eq of is Iso restrict
-- statement:
--   The Map Comap Iso construction uses the map comap ideal eq of is Iso restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapIdealSheafEqOfIsIsoRestrict.lean#L27-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapIdealSheafEqOfIsIsoRestrict.lean#L27-L53

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

theorem GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict :
    ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) →
      ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U →
        ((τ.comap π).map π).ideal V = τ.ideal V := by sorry
