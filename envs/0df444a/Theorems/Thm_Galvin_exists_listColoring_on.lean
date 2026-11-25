-- Prove2me | Theorems.Thm_Galvin_exists_listColoring_on
-- name    : Galvin.exists_listColoring_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:05:49.504472+00:00
-- url     : https://prove2.me/theorems/bc505f5f-0b3e-48cf-bae9-e2f3a925780c
-- title:
--   Galvin: exists list Coloring on
-- statement:
--   The Galvin construction uses the exists list Coloring on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Kernel.lean#L33-L101
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Kernel.lean#L33-L101

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_GalvinLib_Kernel
set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset

theorem Galvin.exists_listColoring_on {α Color : Type*} [Nonempty Color]
    (G : SimpleGraph α) (D : α → α → Prop) [DecidableRel D] (hK : HasKernels G D) :
    ∀ (n : ℕ) (U : Finset α), U.card = n → ∀ L : α → Finset Color,
      (∀ x ∈ U, (U.filter (D x ·)).card < (L x).card) →
      ∃ c : α → Color, (∀ x ∈ U, c x ∈ L x) ∧
        ∀ x ∈ U, ∀ y ∈ U, G.Adj x y → c x ≠ c y := by sorry
