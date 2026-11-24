-- Prove2me | Theorems.Thm_GlobalTheory_T_map_comap_idealSheaf_eq_of_isIso_restrict
-- name    : GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:52.051704+00:00
-- url     : https://prove2.me/theorems/d1f6f97c-343a-4f57-8dc2-800b7d2e955f
-- title:
--   T: map comap ideal Sheaf eq of is Iso restrict
-- statement:
--   The T construction uses the map comap ideal Sheaf eq of is Iso restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapIdealSheafEqOfIsIsoRestrictStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapIdealSheafEqOfIsIsoRestrictStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrictStatement
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

theorem GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict : ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U → ((τ.comap π).map π).ideal V = τ.ideal V := by sorry
