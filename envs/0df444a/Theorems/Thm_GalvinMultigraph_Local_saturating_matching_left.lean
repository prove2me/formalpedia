-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_saturating_matching_left
-- name    : GalvinMultigraph.Local.saturating_matching_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:50:39.161229+00:00
-- url     : https://prove2.me/theorems/2d6641fa-4501-4c60-9f9f-0b2e1b890c4b
-- title:
--   Local: saturating matching left
-- statement:
--   Hall's theorem: a matching of `S` saturating every left vertex of maximal degree `Δ`.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L75-L132
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L75-L132

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
omit [Fintype R] [Fintype E]

theorem GalvinMultigraph.Local.saturating_matching_left (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      ∀ u, degLOn left S u = Δ → ∃ e ∈ M, left e = u := by sorry
