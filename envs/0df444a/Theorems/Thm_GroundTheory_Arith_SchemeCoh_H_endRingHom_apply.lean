-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_H_endRingHom_apply
-- name    : GroundTheory.Arith.SchemeCoh.H.endRingHom_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:27.859932+00:00
-- url     : https://prove2.me/theorems/48cec26c-9cb8-5a09-9684-02bac46f7504
-- title:
--   H: end Ring Hom apply
-- statement:
--   The H construction uses the end Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L33-L34

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Linear
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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
universe w' w v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

theorem GroundTheory.Arith.SchemeCoh.H.endRingHom_apply (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (f : End G)
    (x : Sheaf.H.{w'} G n) : H.endRingHom G n f x = Sheaf.H.map f n x := by sorry
