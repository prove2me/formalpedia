-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_LocalizingAction_act_zero
-- name    : GroundTheory.Arith.SchemeCoh.LocalizingAction.act_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:14.216826+00:00
-- url     : https://prove2.me/theorems/f8b6b1fd-5264-419f-ba3a-e00b0ef22507
-- title:
--   Localizing Action: act zero
-- statement:
--   The Localizing Action construction uses the act zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L37-L40

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
open GroundTheory.Arith.SchemeCoh.LocalizingAction

theorem GroundTheory.Arith.SchemeCoh.LocalizingAction.act_zero (W : Opens X) (x : P.obj (op W)) : A.act 0 W x = 0 := by sorry
