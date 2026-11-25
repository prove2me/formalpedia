-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_H_linearMap_apply
-- name    : GroundTheory.Arith.SchemeCoh.H.linearMap_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:50.121373+00:00
-- url     : https://prove2.me/theorems/5aab1cf6-0924-50da-9ea5-0d4cbeecd9c8
-- title:
--   H: linear Map apply
-- statement:
--   The H construction uses the linear Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L163-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L163-L164

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
variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

theorem GroundTheory.Arith.SchemeCoh.H.linearMap_apply {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) (x : Sheaf.H.{w'} (modulesAb F) n) :
    H.linearMap A φ n x = Sheaf.H.map.{w'} (modulesAbMap φ) n x := by sorry
