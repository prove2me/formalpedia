-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_H_map_g_map_f
-- name    : GroundTheory.Arith.SchemeCoh.H.map_g_map_f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:40.912639+00:00
-- url     : https://prove2.me/theorems/1b15e0a5-17be-4e8a-909b-67e12d1c2c44
-- title:
--   H: map g map f
-- statement:
--   The H construction uses the map g map f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L189-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L189-L191

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
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

theorem GroundTheory.Arith.SchemeCoh.H.map_g_map_f {n : ℕ} (x : Sheaf.H S.X₁ n) :
    Sheaf.H.map S.g n (Sheaf.H.map S.f n x) = 0 := by sorry
