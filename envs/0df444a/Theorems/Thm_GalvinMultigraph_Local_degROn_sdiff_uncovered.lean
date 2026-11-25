-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_degROn_sdiff_uncovered
-- name    : GalvinMultigraph.Local.degROn_sdiff_uncovered
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:26:55.536829+00:00
-- url     : https://prove2.me/theorems/459ff750-e21d-40b0-96cb-75ae48a9d0a8
-- title:
--   Local: deg ROn sdiff uncovered
-- statement:
--   The Local construction uses the deg ROn sdiff uncovered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L122-L128
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L122-L128

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
omit [Fintype R] [Fintype E]

theorem GalvinMultigraph.Local.degROn_sdiff_uncovered (right : E → R) (S M : Finset E) (v : R)
    (h : ∀ m ∈ M, right m ≠ v) : degROn right (S \ M) v = degROn right S v := by sorry
