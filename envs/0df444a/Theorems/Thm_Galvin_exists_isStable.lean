-- Prove2me | Theorems.Thm_Galvin_exists_isStable
-- name    : Galvin.exists_isStable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:37:47.634719+00:00
-- url     : https://prove2.me/theorems/19677455-5dc9-4cd7-b3e1-9acd5bb2b381
-- title:
--   Galvin: exists is Stable
-- statement:
--   The Galvin construction uses the exists is Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/GaleShapley.lean#L67-L103
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/GaleShapley.lean#L67-L103

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Mathlib.Data.Set.Card
public import Definitions.Def_GalvinLib_GaleShapley
set_option autoImplicit true
@[expose] public section
public section
open Galvin

theorem Galvin.exists_isStable {M W : Type*} [Finite M] [Finite W]
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∀ (n : ℕ) (E : M → W → Prop), {p : M × W | E p.1 p.2}.ncard = n →
      ∃ μ, IsStable E rm rw μ := by sorry
