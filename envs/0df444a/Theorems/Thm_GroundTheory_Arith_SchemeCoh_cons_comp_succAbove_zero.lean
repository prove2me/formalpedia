-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_zero
-- name    : GroundTheory.Arith.SchemeCoh.cons_comp_succAbove_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:43.337304+00:00
-- url     : https://prove2.me/theorems/3ccca4fb-a326-4acf-b79d-38a7da1ea3ec
-- title:
--   Scheme Coh: cons comp succ Above zero
-- statement:
--   The Scheme Coh construction uses the cons comp succ Above zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L202-L205

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
variable (A : X → AddCommGrpCat.{u})

theorem GroundTheory.Arith.SchemeCoh.cons_comp_succAbove_zero {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by sorry
