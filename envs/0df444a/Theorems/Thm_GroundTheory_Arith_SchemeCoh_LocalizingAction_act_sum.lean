-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_LocalizingAction_act_sum
-- name    : GroundTheory.Arith.SchemeCoh.LocalizingAction.act_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:49.604616+00:00
-- url     : https://prove2.me/theorems/2d3b1091-d7c9-429c-ae2a-7a8562036c0c
-- title:
--   Localizing Action: act sum
-- statement:
--   The Localizing Action construction uses the act sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L42-L47

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

theorem GroundTheory.Arith.SchemeCoh.LocalizingAction.act_sum {α : Type*} (s : Finset α) (c : α → R) (W : Opens X) (x : P.obj (op W)) :
    A.act (∑ a ∈ s, c a) W x = ∑ a ∈ s, A.act (c a) W x := by sorry
