-- Prove2me | Theorems.Thm_Hamiltonicity_chvatal_erdos
-- name    : Hamiltonicity.chvatal_erdos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:19:19.979486+00:00
-- url     : https://prove2.me/theorems/6c89fdb6-d868-47f8-9d02-2b97a0d67890
-- title:
--   Hamiltonicity: chvatal erdos
-- statement:
--   **Chvátal–Erdős (1972).** A `k`-connected graph on at least three vertices whose independent
--   sets have at most `k` vertices is Hamiltonian.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean#L100-L104
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean#L100-L104

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

theorem Hamiltonicity.chvatal_erdos [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (k : ℕ)
    (hk : IsKConnected G k) (hα : ∀ s : Set V, G.IsIndepSet s → s.ncard ≤ k) :
    G.IsHamiltonian := by sorry
