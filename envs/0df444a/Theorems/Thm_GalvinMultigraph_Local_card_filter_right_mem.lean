-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_card_filter_right_mem
-- name    : GalvinMultigraph.Local.card_filter_right_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:22:11.682801+00:00
-- url     : https://prove2.me/theorems/e2e43f3f-705c-4c30-8edf-208fd9eb07f9
-- title:
--   Local: card filter right mem
-- statement:
--   Edges of `S` whose right endpoint lies in `B`, counted fibrewise.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L61-L71
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L61-L71

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
omit [Fintype R] [Fintype E] [DecidableEq E]

theorem GalvinMultigraph.Local.card_filter_right_mem (right : E → R) (S : Finset E) (B : Finset R) :
    (S.filter fun e => right e ∈ B).card = ∑ r ∈ B, degROn right S r := by sorry
