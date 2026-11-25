-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_stable_matching_multi
-- name    : GalvinMultigraph.Local.stable_matching_multi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:50:40.794166+00:00
-- url     : https://prove2.me/theorems/3c688350-a639-432e-a038-3e60099d91a8
-- title:
--   Local: stable matching multi
-- statement:
--   **Stable matchings for bipartite multigraphs.**  If every vertex ranks its incident edges
--   injectively (`pu` at the left endpoints, `pr` at the right endpoints, larger = better), then any set
--   `S` of edges has a stable matching: a matching `M ⊆ S` such that every edge of `S` outside `M` is
--   beaten, at one of its two endpoints, by an edge of `M`.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Stable.lean#L51-L113
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Stable.lean#L51-L113

module
public import Definitions.Def_GalvinMultigraph_Local_Base
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
public import Definitions.Def_GalvinMultigraph_Local_Stable
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

theorem GalvinMultigraph.Local.stable_matching_multi (left : E → U) (right : E → R) (pu pr : E → ℕ)
    (hu : ∀ e f, left e = left f → pu e = pu f → e = f)
    (hr : ∀ e f, right e = right f → pr e = pr f → e = f) (S : Finset E) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      ∀ g ∈ S, g ∉ M → (∃ f ∈ M, left f = left g ∧ pu g < pu f) ∨
        (∃ f ∈ M, right f = right g ∧ pr g < pr f) := by sorry
