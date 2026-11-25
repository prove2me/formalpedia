-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_degLOn_le_of_subset
-- name    : GalvinMultigraph.Local.degLOn_le_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:24:33.058939+00:00
-- url     : https://prove2.me/theorems/8a26d31e-3e4c-4951-854d-5f6e8bcb14c2
-- title:
--   Local: deg LOn le of subset
-- statement:
--   The Local construction uses the deg LOn le of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L57-L59
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L57-L59

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
omit [Fintype U] [Fintype E] [DecidableEq E]

theorem GalvinMultigraph.Local.degLOn_le_of_subset (left : E → U) {S T : Finset E} (h : S ⊆ T) (u : U) :
    degLOn left S u ≤ degLOn left T u := by sorry
