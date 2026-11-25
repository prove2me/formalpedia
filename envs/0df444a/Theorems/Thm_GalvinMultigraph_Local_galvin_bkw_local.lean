-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_galvin_bkw_local
-- name    : GalvinMultigraph.Local.galvin_bkw_local
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:29:23.340891+00:00
-- url     : https://prove2.me/theorems/3a4be9cd-e8c4-4604-bb9d-06c30d0148e2
-- title:
--   Local: galvin bkw local
-- statement:
--   **Theorem B (Borodin–Kostochka–Woodall, local lists).** Bipartite multigraph; if every edge `e
--       = uv` has a
--   list of size ≥ max(d(u), d(v)), there is a proper list edge colouring.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Main.lean#L196-L276
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Main.lean#L196-L276

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

theorem GalvinMultigraph.Local.galvin_bkw_local (left : E → U) (right : E → R)
    (L : E → Finset ℕ) (hL : ∀ e, max (degL left (left e)) (degR right (right e)) ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by sorry
