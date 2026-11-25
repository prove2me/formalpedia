-- Prove2me | Theorems.Thm_ListEdgeColouring_gale_shapley
-- name    : ListEdgeColouring.gale_shapley
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:10:45.232809+00:00
-- url     : https://prove2.me/theorems/fe16ebef-ae26-4393-90df-fda0cfc36e63
-- title:
--   List Edge Colouring: gale shapley
-- statement:
--   **Gale–Shapley (1962).** For a bipartite acceptability relation `E` between finite sets `M`
--   and `W`, with strict preferences given by injective rank functions (`rm m w < rm m w'` means that
--   `m` prefers `w` to `w'`), there is a stable matching.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Solution.lean#L34-L41
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Solution.lean#L34-L41

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_GalvinMultigraph
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinDinitzSolution
public import Theorems.Thm_Galvin_gale_shapley

set_option autoImplicit true
@[expose] public section
public section
open ListEdgeColouring

theorem ListEdgeColouring.gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by sorry
