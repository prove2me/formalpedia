-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_degROn_sdiff_covered
-- name    : GalvinMultigraph.Local.degROn_sdiff_covered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:25:21.860448+00:00
-- url     : https://prove2.me/theorems/4401674e-6529-4dc4-a791-c9ca03591832
-- title:
--   Local: deg ROn sdiff covered
-- statement:
--   Deleting a matching drops the right degree of a covered vertex by exactly one.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L91-L110
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L91-L110

module
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
public import Definitions.Def_GalvinMultigraph_Local_Ranks
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
omit [Fintype U] [Fintype R] [Fintype E] [DecidableEq U]

theorem GalvinMultigraph.Local.degROn_sdiff_covered (left : E → U) (right : E → R) (S M : Finset E)
    (hM : IsMatchingOn left right M) (hMS : M ⊆ S) {m : E} (hm : m ∈ M) :
    degROn right S (right m) = degROn right (S \ M) (right m) + 1 := by sorry
