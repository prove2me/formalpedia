-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_LocalizingAction_bijective_pow
-- name    : GroundTheory.Arith.SchemeCoh.LocalizingAction.bijective_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:04.389928+00:00
-- url     : https://prove2.me/theorems/01d78cbc-c7e6-4be5-9632-3bf8dfb41d9b
-- title:
--   Localizing Action: bijective pow
-- statement:
--   The Localizing Action construction uses the bijective pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L49-L60

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

theorem GroundTheory.Arith.SchemeCoh.LocalizingAction.bijective_pow (g : R) (W : Opens X) (hW : W ≤ D g) (L : ℕ) :
    Function.Bijective (A.act (g ^ L) W) := by sorry
