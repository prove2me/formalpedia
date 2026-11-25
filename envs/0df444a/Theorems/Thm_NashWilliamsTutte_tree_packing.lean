-- Prove2me | Theorems.Thm_NashWilliamsTutte_tree_packing
-- name    : NashWilliamsTutte.tree_packing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:35:20.662652+00:00
-- url     : https://prove2.me/theorems/99a9fb84-f7d0-4a3b-865e-87abc0845559
-- title:
--   Nash Williams Tutte: tree packing
-- statement:
--   **Nash-Williams–Tutte tree packing theorem.** A finite graph on a nonempty vertex type has `k`
--   pairwise edge-disjoint spanning trees if and only if, for every map `f : V → V`, the number of
--   edges of `G` whose endpoints have different images under `f` is at least `k` times the number of
--   nonempty fibres of `f` minus one.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/Solution.lean#L33-L39
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/Solution.lean#L33-L39

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliams
public import Definitions.Def_NashWilliamsTrees_Solution
public import Theorems.Thm_NashWilliams_tree_packing

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliamsTutte

theorem NashWilliamsTutte.tree_packing {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (k : ℕ) :
    (∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
        Pairwise fun i j ↦ Disjoint (T i) (T j)) ↔
      ∀ f : V → V,
        k * (#(univ.image f) - 1) ≤ (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet.ncard := by sorry
