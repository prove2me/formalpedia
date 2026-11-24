-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_comp_apply_eq_zero
-- name    : GroundTheory.Arith.SchemeCoh.app_comp_apply_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:33.698274+00:00
-- url     : https://prove2.me/theorems/72c786dc-46af-4026-a2ec-1309e710af28
-- title:
--   Scheme Coh: app comp apply eq zero
-- statement:
--   The Scheme Coh construction uses the app comp apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L139-L142

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
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
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

theorem GroundTheory.Arith.SchemeCoh.app_comp_apply_eq_zero (W : (Opens X)ᵒᵖ) (x : S.X₁.obj.obj W) :
    S.g.hom.app W (S.f.hom.app W x) = 0 := by sorry
