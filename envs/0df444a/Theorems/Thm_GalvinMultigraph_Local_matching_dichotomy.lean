-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_matching_dichotomy
-- name    : GalvinMultigraph.Local.matching_dichotomy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:28:17.489568+00:00
-- url     : https://prove2.me/theorems/67a34f48-7593-45eb-a1f5-ff1cbf42a101
-- title:
--   Local: matching dichotomy
-- statement:
--   **The peeling dichotomy.**  A nonempty set of edges contains a nonempty matching which either
--   covers every left vertex that carries an edge, or is such that every neighbour of a covered left
--   vertex is covered on the right.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L216-L284
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L216-L284

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

theorem GalvinMultigraph.Local.matching_dichotomy (left : E → U) (right : E → R) (S : Finset E) (hS : S.Nonempty) :
    ∃ M : Finset E, M ⊆ S ∧ M.Nonempty ∧ IsMatchingOn left right M ∧
      ((∀ e ∈ S, ∃ f ∈ M, left f = left e) ∨
       (∀ e ∈ S, (∃ f ∈ M, left f = left e) → ∃ f ∈ M, right f = right e)) := by sorry
