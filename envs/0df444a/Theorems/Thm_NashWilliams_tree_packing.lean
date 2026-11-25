-- Prove2me | Theorems.Thm_NashWilliams_tree_packing
-- name    : NashWilliams.tree_packing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:46:00.628957+00:00
-- url     : https://prove2.me/theorems/a990b6e2-1544-4af6-ab1a-12b7f2dad043
-- title:
--   Nash Williams: tree packing
-- statement:
--   **Nash-Williams–Tutte tree packing theorem.** A finite graph on a nonempty vertex type has `k`
--   pairwise edge-disjoint spanning trees if and only if, for every map `f : V → V`, the number of
--   edges of `G` whose endpoints have different images under `f` is at least `k` times the number of
--   nonempty fibres of `f` minus one.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliams.lean#L41-L110
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliams.lean#L41-L110

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Definitions.Def_TreePackingLib_NashWilliams
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliams

theorem NashWilliams.tree_packing {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (k : ℕ) :
    (∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
        Pairwise fun i j ↦ Disjoint (T i) (T j)) ↔
      ∀ f : V → V,
        k * (#(univ.image f) - 1) ≤ (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet.ncard := by sorry
