-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_galvin_multigraph_max_degree
-- name    : GalvinMultigraph.Local.galvin_multigraph_max_degree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:08:52.181821+00:00
-- url     : https://prove2.me/theorems/e2c1f49d-fcd1-404d-9240-10ac7a048d56
-- title:
--   Local: galvin multigraph max degree
-- statement:
--   **Theorem A (Galvin, multigraph, maximum degree).** Bipartite multigraph with all degrees ≤ Δ
--       and lists of
--   size ≥ Δ has a proper list edge colouring.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Main.lean#L118-L191
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Main.lean#L118-L191

module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Set
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_GalvinMultigraph_Local_Kernel
public import Definitions.Def_GalvinMultigraph_Local_Ranks
public import Definitions.Def_GalvinMultigraph_Local_Main
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E] [DecidableEq U] [DecidableEq R]
    [DecidableEq E]

theorem GalvinMultigraph.Local.galvin_multigraph_max_degree (left : E → U) (right : E → R) (Δ : ℕ)
    (hdegU : ∀ u, degL left u ≤ Δ) (hdegR : ∀ r, degR right r ≤ Δ)
    (L : E → Finset ℕ) (hL : ∀ e, Δ ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by sorry
