-- Prove2me | Theorems.Thm_NashWilliamsTutte_arboricity
-- name    : NashWilliamsTutte.arboricity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:45.860124+00:00
-- url     : https://prove2.me/theorems/42c6ecfd-7e82-57a2-a8dd-ce73b25af935
-- title:
--   Nash Williams Tutte: arboricity
-- statement:
--   **Nash-Williams' arboricity theorem.** The edges of a finite graph can be covered by `k`
--   forests if and only if every nonempty set `S` of vertices spans at most `k (#S - 1)` edges.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/Solution.lean#L43-L46
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/Solution.lean#L43-L46

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliams
public import Definitions.Def_NashWilliamsTrees_Solution
public import Theorems.Thm_NashWilliams_arboricity

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliamsTutte

theorem NashWilliamsTutte.arboricity {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    (∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ G = ⨆ i, F i) ↔
      ∀ S : Finset V, S.Nonempty → (G.induce (S : Set V)).edgeSet.ncard ≤ k * (#S - 1) := by sorry
