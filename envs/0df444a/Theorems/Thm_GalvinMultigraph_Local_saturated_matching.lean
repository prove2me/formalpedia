-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_saturated_matching
-- name    : GalvinMultigraph.Local.saturated_matching
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:23:56.64014+00:00
-- url     : https://prove2.me/theorems/253d4a5c-fa29-429f-914f-a010d62ba211
-- title:
--   Local: saturated matching
-- statement:
--   A matching of `S` meeting every vertex of degree exactly `Δ`, on both sides.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L217-L225
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L217-L225

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

theorem GalvinMultigraph.Local.saturated_matching (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hL : ∀ u, degLOn left S u ≤ Δ) (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      (∀ u, degLOn left S u = Δ → ∃ e ∈ M, left e = u) ∧
      (∀ r, degROn right S r = Δ → ∃ e ∈ M, right e = r) := by sorry
