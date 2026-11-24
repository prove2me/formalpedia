-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_id
-- name    : GroundTheory.Arith.SchemeCoh.push_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:34.584478+00:00
-- url     : https://prove2.me/theorems/61ba0b9c-dc10-4fb0-9cbd-c9e69365bbfc
-- title:
--   Scheme Coh: push id
-- statement:
--   The Scheme Coh construction uses the push id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L107-L109

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

theorem GroundTheory.Arith.SchemeCoh.push_id (n : ℕ) (σ : Cochain P U n) : push U (𝟙 P) n σ = σ := by sorry
