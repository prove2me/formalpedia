-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_degROn_pos
-- name    : GalvinMultigraph.Local.degROn_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:28:04.667697+00:00
-- url     : https://prove2.me/theorems/b0436ca3-bd25-4ab8-b842-a7a0734648fd
-- title:
--   Local: deg ROn pos
-- statement:
--   The Local construction uses the deg ROn pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L136-L138
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L136-L138

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
omit [Fintype R] [Fintype E] [DecidableEq E]

theorem GalvinMultigraph.Local.degROn_pos (right : E → R) {S : Finset E} {e : E} (he : e ∈ S) :
    0 < degROn right S (right e) := by sorry
