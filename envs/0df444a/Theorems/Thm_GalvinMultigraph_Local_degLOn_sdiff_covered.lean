-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_degLOn_sdiff_covered
-- name    : GalvinMultigraph.Local.degLOn_sdiff_covered
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:25:14.008817+00:00
-- url     : https://prove2.me/theorems/841b3ff9-d3e2-422f-9f72-3e2629d3eb89
-- title:
--   Local: deg LOn sdiff covered
-- statement:
--   Deleting a matching drops the left degree of a covered vertex by exactly one.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L68-L87
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L68-L87

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
omit [Fintype U] [Fintype R] [Fintype E] [DecidableEq R]

theorem GalvinMultigraph.Local.degLOn_sdiff_covered (left : E → U) (right : E → R) (S M : Finset E)
    (hM : IsMatchingOn left right M) (hMS : M ⊆ S) {m : E} (hm : m ∈ M) :
    degLOn left S (left m) = degLOn left (S \ M) (left m) + 1 := by sorry
