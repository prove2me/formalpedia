-- Prove2me | Theorems.Thm_Menger_isEdgeConnected_iff
-- name    : Menger.isEdgeConnected_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:11:05.503066+00:00
-- url     : https://prove2.me/theorems/aeabf259-4777-47c0-be33-5d45b27e54b3
-- title:
--   Menger: is Edge Connected iff
-- statement:
--   **Menger's theorem, global edge form.** A finite graph is `k`-edge-connected if and only if any
--   two vertices are joined by `k` pairwise edge-disjoint paths.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L239-L244
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L239-L244

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

theorem Menger.isEdgeConnected_iff [Finite V] (G : SimpleGraph V) (k : ℕ) :
    G.IsEdgeConnected k ↔
      ∀ u v : V, ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by sorry
