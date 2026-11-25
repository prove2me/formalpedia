-- Prove2me | Theorems.Thm_NashWilliams_arboricity
-- name    : NashWilliams.arboricity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:46:12.834785+00:00
-- url     : https://prove2.me/theorems/f84c44d1-21c7-4fa3-9c79-e69fa0658591
-- title:
--   Nash Williams: arboricity
-- statement:
--   **Nash-Williams' arboricity theorem.** The edges of a finite graph can be covered by `k`
--   forests if and only if every nonempty set `S` of vertices spans at most `k (#S - 1)` edges.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliams.lean#L114-L185
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliams.lean#L114-L185

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Definitions.Def_TreePackingLib_NashWilliams
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliams

theorem NashWilliams.arboricity {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    (∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ G = ⨆ i, F i) ↔
      ∀ S : Finset V, S.Nonempty → (G.induce (S : Set V)).edgeSet.ncard ≤ k * (#S - 1) := by sorry
