-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_konig_multigraph
-- name    : GalvinMultigraph.Local.konig_multigraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:24:25.526106+00:00
-- url     : https://prove2.me/theorems/acd7a1e7-1c8c-47c6-8726-6dbae065bd1b
-- title:
--   Local: konig multigraph
-- statement:
--   **Kőnig's edge colouring theorem for bipartite multigraphs.**  A set `S` of edges with all
--   degrees at most `Δ` has a proper edge colouring with colours `< Δ`.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L229-L298
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L229-L298

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

theorem GalvinMultigraph.Local.konig_multigraph (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ)
    (hL : ∀ u, degLOn left S u ≤ Δ) (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ φ : E → ℕ, (∀ e ∈ S, φ e < Δ) ∧
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by sorry
