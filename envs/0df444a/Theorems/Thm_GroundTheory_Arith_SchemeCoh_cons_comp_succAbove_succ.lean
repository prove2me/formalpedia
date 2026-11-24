-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_succ
-- name    : GroundTheory.Arith.SchemeCoh.cons_comp_succAbove_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:26.481018+00:00
-- url     : https://prove2.me/theorems/02a6cc3f-59b8-4520-afff-22c53b975dd3
-- title:
--   Scheme Coh: cons comp succ Above succ
-- statement:
--   The Scheme Coh construction uses the cons comp succ Above succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L207-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L207-L212

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

theorem GroundTheory.Arith.SchemeCoh.cons_comp_succAbove_succ {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons c (i ∘ k.succAbove) := by sorry
