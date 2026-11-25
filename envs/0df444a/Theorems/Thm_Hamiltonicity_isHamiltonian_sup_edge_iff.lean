-- Prove2me | Theorems.Thm_Hamiltonicity_isHamiltonian_sup_edge_iff
-- name    : Hamiltonicity.isHamiltonian_sup_edge_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:16:21.97873+00:00
-- url     : https://prove2.me/theorems/7a1802f5-b4e8-56a9-83a1-b2a5c49cd672
-- title:
--   Hamiltonicity: is Hamiltonian sup edge iff
-- statement:
--   **Bondy–Chvátal (1976).** Adding an edge between two non-adjacent vertices whose degrees sum
--   to at least `n` does not change whether the graph is Hamiltonian.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean#L46-L50
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean#L46-L50

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_ClosureAux
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_MengerHamilton_Hamiltonian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.isHamiltonian_sup_edge_iff [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian := by sorry
