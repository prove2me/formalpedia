-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_saturating_matching_right
-- name    : GalvinMultigraph.Local.saturating_matching_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:22:57.248867+00:00
-- url     : https://prove2.me/theorems/61c5bc8b-b568-44d6-8aff-cfc2ed56bdfe
-- title:
--   Local: saturating matching right
-- statement:
--   Hall's theorem: a matching of `S` saturating every right vertex of maximal degree `Δ`.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L136-L141
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Konig.lean#L136-L141

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
omit [Fintype U] [Fintype E]

theorem GalvinMultigraph.Local.saturating_matching_right (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hL : ∀ u, degLOn left S u ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      ∀ r, degROn right S r = Δ → ∃ e ∈ M, right e = r := by sorry
