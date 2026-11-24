-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ev_res
-- name    : GroundTheory.Arith.SchemeCoh.ev_res
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:40.738881+00:00
-- url     : https://prove2.me/theorems/1765f400-f5a5-49a6-87f6-76fa2483bfcb
-- title:
--   Scheme Coh: ev res
-- statement:
--   The Scheme Coh construction uses the ev res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L178-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L178-L179

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
attribute [local semireducible] inter

theorem GroundTheory.Arith.SchemeCoh.ev_res {V W : Opens X} (h : V ≤ W) (s : (discPresheaf A).obj (op W)) (x : X) (hx : x ∈ V) :
    ev A x hx (res (discPresheaf A) h s) = ev A x (h hx) s := by sorry
