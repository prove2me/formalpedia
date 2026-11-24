-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_d
-- name    : GroundTheory.Arith.SchemeCoh.push_d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:24.322274+00:00
-- url     : https://prove2.me/theorems/1a7d1a6a-8c6e-4c57-82a4-1e166b7b16b1
-- title:
--   Scheme Coh: push d
-- statement:
--   The Scheme Coh construction uses the push d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L95-L98

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

theorem GroundTheory.Arith.SchemeCoh.push_d {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ) (σ : Cochain P U n) :
    push U φ (n + 1) (d P U n σ) = d P' U n (push U φ n σ) := by sorry
