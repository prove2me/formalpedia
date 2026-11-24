-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_injective
-- name    : GroundTheory.Arith.SchemeCoh.push_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:19.77692+00:00
-- url     : https://prove2.me/theorems/b9d4a74f-53d5-4bd6-89b1-89ee7e3cbd32
-- title:
--   Scheme Coh: push injective
-- statement:
--   The Scheme Coh construction uses the push injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L121-L124

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

theorem GroundTheory.Arith.SchemeCoh.push_injective {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ)
    (h : ∀ i : Fin (n + 1) → ι, Function.Injective (φ.app (op (inter U i)))) :
    Function.Injective (push U φ n) := by sorry
