-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_freeYonedaHomAddEquiv_apply
-- name    : GroundTheory.Arith.SchemeCoh.freeYonedaHomAddEquiv_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:45.119442+00:00
-- url     : https://prove2.me/theorems/ecfb07d5-0f53-4d87-a908-b9637ddd7e0a
-- title:
--   Scheme Coh: free Yoneda Hom Add Equiv apply
-- statement:
--   The Scheme Coh construction uses the free Yoneda Hom Add Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L69-L71

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

theorem GroundTheory.Arith.SchemeCoh.freeYonedaHomAddEquiv_apply (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (g : yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) :
    freeYonedaHomAddEquiv U P g = g.app (op U) (FreeAbelianGroup.of (𝟙 U)) := by sorry
