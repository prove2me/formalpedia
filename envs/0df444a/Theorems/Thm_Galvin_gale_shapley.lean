-- Prove2me | Theorems.Thm_Galvin_gale_shapley
-- name    : Galvin.gale_shapley
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:44.716389+00:00
-- url     : https://prove2.me/theorems/48603126-315e-435c-aebf-205440f31b5e
-- title:
--   Galvin: gale shapley
-- statement:
--   **Gale–Shapley (1962).** For a bipartite acceptability relation `E` between finite sets `M`
--   and `W`, with strict preferences given by injective rank functions (`rm m w < rm m w'` means that
--   `m` prefers `w` to `w'`), there is a stable matching.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Galvin.lean#L39-L46
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Galvin.lean#L39-L46

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_Konig_Basic
public import Definitions.Def_GalvinLib_Orientation
public import Definitions.Def_GalvinLib_Galvin
set_option autoImplicit true
@[expose] public section
public section
open Galvin

theorem Galvin.gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by sorry
