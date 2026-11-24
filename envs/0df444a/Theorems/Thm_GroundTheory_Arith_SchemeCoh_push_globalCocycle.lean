-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_globalCocycle
-- name    : GroundTheory.Arith.SchemeCoh.push_globalCocycle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:30.683263+00:00
-- url     : https://prove2.me/theorems/11e1dbb4-3d79-4d9b-98bc-bd40eadb8f7e
-- title:
--   Scheme Coh: push global Cocycle
-- statement:
--   The Scheme Coh construction uses the push global Cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechLeray.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechLeray.lean#L204-L207

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
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
noncomputable section
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w w' u
variable {X : TopCat.{u}}
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable {P}

theorem GroundTheory.Arith.SchemeCoh.push_globalCocycle {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P')
    (s : P.obj (op ⊤)) :
    push U φ 0 (globalCocycle P U s).1 = (globalCocycle P' U (φ.app _ s)).1 := by sorry
