-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_degLOn_sdiff_uncovered
-- name    : GalvinMultigraph.Local.degLOn_sdiff_uncovered
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:25:40.602741+00:00
-- url     : https://prove2.me/theorems/a9445cd9-6a35-45be-887a-33ed677089ff
-- title:
--   Local: deg LOn sdiff uncovered
-- statement:
--   The Local construction uses the deg LOn sdiff uncovered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L113-L119
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L113-L119

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
omit [Fintype U] [Fintype E]

theorem GalvinMultigraph.Local.degLOn_sdiff_uncovered (left : E → U) (S M : Finset E) (u : U)
    (h : ∀ m ∈ M, left m ≠ u) : degLOn left (S \ M) u = degLOn left S u := by sorry
