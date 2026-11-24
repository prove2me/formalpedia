-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_freeYonedaHomAddEquiv_naturality_left
-- name    : GroundTheory.Arith.SchemeCoh.freeYonedaHomAddEquiv_naturality_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:43.228097+00:00
-- url     : https://prove2.me/theorems/da001b1f-194f-46dc-8d56-85c83b4210c0
-- title:
--   Scheme Coh: free Yoneda Hom Add Equiv naturality left
-- statement:
--   The Scheme Coh construction uses the free Yoneda Hom Add Equiv naturality left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L73-L82

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
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
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

theorem GroundTheory.Arith.SchemeCoh.freeYonedaHomAddEquiv_naturality_left {U V : C} (f : U ⟶ V) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (g : yoneda.obj V ⋙ AddCommGrpCat.free.{v} ⟶ P) :
    freeYonedaHomAddEquiv U P (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free ≫ g) =
      P.map f.op (freeYonedaHomAddEquiv V P g) := by sorry
