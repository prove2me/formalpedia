-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_degROn_le_of_subset
-- name    : GalvinMultigraph.Local.degROn_le_of_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:24:58.511246+00:00
-- url     : https://prove2.me/theorems/73ba307a-9790-4354-a3da-8714bf4ccffb
-- title:
--   Local: deg ROn le of subset
-- statement:
--   The Local construction uses the deg ROn le of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L62-L64
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L62-L64

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

theorem GalvinMultigraph.Local.degROn_le_of_subset (right : E → R) {S T : Finset E} (h : S ⊆ T) (r : R) :
    degROn right S r ≤ degROn right T r := by sorry
