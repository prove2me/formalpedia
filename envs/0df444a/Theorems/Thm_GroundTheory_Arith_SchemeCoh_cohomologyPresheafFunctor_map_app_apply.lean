-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_cohomologyPresheafFunctor_map_app_apply
-- name    : GroundTheory.Arith.SchemeCoh.cohomologyPresheafFunctor_map_app_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:49.59493+00:00
-- url     : https://prove2.me/theorems/793b2f93-929d-447c-8732-bde4960baf5d
-- title:
--   Scheme Coh: cohomology Presheaf Functor map app apply
-- statement:
--   The Scheme Coh construction uses the cohomology Presheaf Functor map app apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L121-L124

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
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

theorem GroundTheory.Arith.SchemeCoh.cohomologyPresheafFunctor_map_app_apply {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G)
    (n : ℕ) (U : C) (x : F.H' n U) :
    ((Sheaf.cohomologyPresheafFunctor J n).map φ).app (op U) x =
      (show Ext (freeSheaf J U) F n from x).comp (Ext.mk₀ φ) (add_zero n) := by sorry
