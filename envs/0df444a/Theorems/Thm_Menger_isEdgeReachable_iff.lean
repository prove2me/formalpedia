-- Prove2me | Theorems.Thm_Menger_isEdgeReachable_iff
-- name    : Menger.isEdgeReachable_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:10:01.691169+00:00
-- url     : https://prove2.me/theorems/0db29ae4-feba-589f-b487-22a5d9664664
-- title:
--   Menger: is Edge Reachable iff
-- statement:
--   **Menger's theorem, edge form.** In a finite graph, `u` and `v` remain connected after the
--   deletion of any fewer than `k` edges if and only if there are `k` pairwise edge-disjoint paths
--   from `u` to `v`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L179-L235
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L179-L235

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Definitions.Def_MengerHamilton_Menger
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger
variable {V : Type*}

theorem Menger.isEdgeReachable_iff [Finite V] (G : SimpleGraph V) (k : ℕ) (u v : V) :
    G.IsEdgeReachable k u v ↔
      ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by sorry
