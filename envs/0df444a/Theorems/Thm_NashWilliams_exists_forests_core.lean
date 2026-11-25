-- Prove2me | Theorems.Thm_NashWilliams_exists_forests_core
-- name    : NashWilliams.exists_forests_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:45:42.685264+00:00
-- url     : https://prove2.me/theorems/4eb11c73-b7c4-4f90-b0c8-07c757e95e10
-- title:
--   Nash Williams: exists forests core
-- statement:
--   **Core exchange lemma.** For every finite graph `G` there are `k` pairwise edge-disjoint
--   forests `F i ≤ G` and a subgraph `H ≤ G` such that each `F i ⊓ H` has the same connected
--   components as `H`, and every edge of `G` outside `H` belongs to some `F i`.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L397-L415
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L397-L415

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}

theorem NashWilliams.exists_forests_core [Finite V] (G : SimpleGraph V) (k : ℕ) :
    ∃ (F : Fin k → SimpleGraph V) (H : SimpleGraph V), (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧
      (Pairwise fun i j ↦ Disjoint (F i) (F j)) ∧ H ≤ G ∧
      (∀ i a b, H.Reachable a b → (F i ⊓ H).Reachable a b) ∧
      (∀ a b, G.Adj a b → ¬ H.Adj a b → ∃ i, (F i).Adj a b) := by sorry
