-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_card_filter_left_mem
-- name    : GalvinMultigraph.Local.card_filter_left_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:22:00.9494+00:00
-- url     : https://prove2.me/theorems/4c36b96d-3ad4-41a0-97f6-053456241b92
-- title:
--   Local: card filter left mem
-- statement:
--   Edges of `S` whose left endpoint lies in `A`, counted fibrewise.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L47-L57
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L47-L57

module
public import Definitions.Def_GalvinMultigraph_Local_Stable
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Set
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Definitions.Def_GalvinMultigraph_Local_Konig
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
omit [Fintype U] [Fintype E] [DecidableEq E]

theorem GalvinMultigraph.Local.card_filter_left_mem (left : E → U) (S : Finset E) (A : Finset U) :
    (S.filter fun e => left e ∈ A).card = ∑ u ∈ A, degLOn left S u := by sorry
