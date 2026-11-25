-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_galvin_engine
-- name    : GalvinMultigraph.Local.galvin_engine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:54.102344+00:00
-- url     : https://prove2.me/theorems/90983c1c-e7ef-4f02-ba02-d67a8290d8eb
-- title:
--   Local: galvin engine
-- statement:
--   **The Galvin engine.**  Given injective rankings of the edges at each vertex (`ru` at the left
--   endpoints, `rv` at the right endpoints), the line graph of the multigraph, oriented towards the
--   larger `ru` at left vertices and towards the smaller `rv` at right vertices, is kernel perfect;
--   hence lists strictly larger than the out-degree suffice.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Main.lean#L66-L113
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Main.lean#L66-L113

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
omit [Fintype U] [Fintype R]

theorem GalvinMultigraph.Local.galvin_engine (left : E → U) (right : E → R) (ru rv : E → ℕ)
    (hru : ∀ e f, left e = left f → ru e = ru f → e = f)
    (hrv : ∀ e f, right e = right f → rv e = rv f → e = f)
    (L : E → Finset ℕ)
    (hL : ∀ e, (Finset.univ.filter fun f =>
        (left e = left f ∧ ru e < ru f) ∨ (right e = right f ∧ rv f < rv e)).card < (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by sorry
