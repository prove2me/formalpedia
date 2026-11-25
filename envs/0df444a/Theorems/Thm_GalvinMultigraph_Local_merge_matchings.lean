-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_merge_matchings
-- name    : GalvinMultigraph.Local.merge_matchings
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:23:31.57812+00:00
-- url     : https://prove2.me/theorems/21457490-0dd0-42b8-97cd-9a2ea50dd5a9
-- title:
--   Local: merge matchings
-- statement:
--   Mendelsohn–Dulmage: two matchings can be merged into a single matching saturating the left
--   vertices covered by the first and the right vertices covered by the second.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L146-L214
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L146-L214

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
omit [Fintype U] [Fintype R]

theorem GalvinMultigraph.Local.merge_matchings (left : E → U) (right : E → R) (S ML MR : Finset E)
    (hMLS : ML ⊆ S) (hMRS : MR ⊆ S)
    (hML : IsMatchingOn left right ML) (hMR : IsMatchingOn left right MR) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      (∀ u, (∃ e ∈ ML, left e = u) → ∃ e ∈ M, left e = u) ∧
      (∀ r, (∃ e ∈ MR, right e = r) → ∃ e ∈ M, right e = r) := by sorry
