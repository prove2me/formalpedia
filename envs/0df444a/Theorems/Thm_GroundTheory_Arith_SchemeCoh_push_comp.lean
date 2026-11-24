-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_comp
-- name    : GroundTheory.Arith.SchemeCoh.push_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:09.299663+00:00
-- url     : https://prove2.me/theorems/d218f670-386d-4af4-b619-636da7bd0f9c
-- title:
--   Scheme Coh: push comp
-- statement:
--   The Scheme Coh construction uses the push comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L101-L104

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

theorem GroundTheory.Arith.SchemeCoh.push_comp {P' P'' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (ψ : P' ⟶ P'')
    (n : ℕ) (σ : Cochain P U n) : push U ψ n (push U φ n σ) = push U (φ ≫ ψ) n σ := by sorry
