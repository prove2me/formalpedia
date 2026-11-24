-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_res
-- name    : GroundTheory.Arith.SchemeCoh.app_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:36.619415+00:00
-- url     : https://prove2.me/theorems/084a3d53-71c8-42bc-8a14-870b9502dc60
-- title:
--   Scheme Coh: app res
-- statement:
--   The Scheme Coh construction uses the app res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L90-L92

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
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
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable {P}
attribute [local semireducible] inter

theorem GroundTheory.Arith.SchemeCoh.app_res {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') {V W : Opens X} (h : V ≤ W)
    (x : P.obj (op W)) : φ.app (op V) (res P h x) = res P' h (φ.app (op W) x) := by sorry
