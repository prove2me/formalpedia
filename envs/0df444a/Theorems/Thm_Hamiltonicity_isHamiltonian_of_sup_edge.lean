-- Prove2me | Theorems.Thm_Hamiltonicity_isHamiltonian_of_sup_edge
-- name    : Hamiltonicity.isHamiltonian_of_sup_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:16:25.508381+00:00
-- url     : https://prove2.me/theorems/17d4c002-6ff2-4ae8-80de-50960e73824f
-- title:
--   Hamiltonicity: is Hamiltonian of sup edge
-- statement:
--   The forward direction of the Bondy–Chvátal closure step.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ClosureAux.lean#L147-L228
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ClosureAux.lean#L147-L228

module
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Definitions.Def_MengerHamilton_ClosureAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.isHamiltonian_of_sup_edge [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v)
    (hH : (G ⊔ edge u v).IsHamiltonian) : G.IsHamiltonian := by sorry
