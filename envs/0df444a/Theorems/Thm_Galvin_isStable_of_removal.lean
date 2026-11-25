-- Prove2me | Theorems.Thm_Galvin_isStable_of_removal
-- name    : Galvin.isStable_of_removal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:55:18.672194+00:00
-- url     : https://prove2.me/theorems/5856c142-42cb-4fcf-9ec2-91e46f196cf1
-- title:
--   Galvin: is Stable of removal
-- statement:
--   The Galvin construction uses the is Stable of removal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/GaleShapley.lean#L49-L65
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/GaleShapley.lean#L49-L65

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

theorem Galvin.isStable_of_removal {M W : Type*} (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ)
    {m₁ m₂ : M} {w : W} (h₁ : IsTop E rm m₁ w) (hlt : rw w m₁ < rw w m₂)
    (μ : M → W → Prop)
    (hμ : IsStable (fun m v => E m v ∧ ¬ (m = m₂ ∧ v = w)) rm rw μ) (hne : m₁ ≠ m₂) :
    IsStable E rm rw μ := by sorry
