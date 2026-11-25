-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_H_smul_def
-- name    : GroundTheory.Arith.SchemeCoh.H.smul_def
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:07:54.44101+00:00
-- url     : https://prove2.me/theorems/a8fe6f0a-1f04-5354-a350-2d1e06934217
-- title:
--   H: smul def
-- statement:
--   The H construction uses the smul def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L150-L152

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

theorem GroundTheory.Arith.SchemeCoh.H.smul_def (F : X.Modules) (n : ℕ) (a : A) (x : Sheaf.H.{w'} (modulesAb F) n) :
    a • x = Sheaf.H.map.{w'} (modulesAbMap
      (smulHom F (algebraMap A Γ(X, ⊤) a))) n x := by sorry
