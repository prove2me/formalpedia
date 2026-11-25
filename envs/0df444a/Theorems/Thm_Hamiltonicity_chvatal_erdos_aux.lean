-- Prove2me | Theorems.Thm_Hamiltonicity_chvatal_erdos_aux
-- name    : Hamiltonicity.chvatal_erdos_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:16:41.631861+00:00
-- url     : https://prove2.me/theorems/abbb02e1-8c12-5bf8-939c-467be1659960
-- title:
--   Hamiltonicity: chvatal erdos aux
-- statement:
--   **Chvátal–Erdős**, with `k`-connectivity unfolded.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L207-L375
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L207-L375

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.chvatal_erdos_aux [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (k : ℕ)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    (hα : ∀ s : Set V, G.IsIndepSet s → s.ncard ≤ k) : G.IsHamiltonian := by sorry
