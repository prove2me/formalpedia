-- Prove2me | Theorems.Thm_Hamiltonicity_exists_cycArr_of_conn
-- name    : Hamiltonicity.exists_cycArr_of_conn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:16:55.119639+00:00
-- url     : https://prove2.me/theorems/4515fe7d-229a-4245-89a7-fd59a613c858
-- title:
--   Hamiltonicity: exists cyc Arr of conn
-- statement:
--   A graph on at least three vertices that stays connected after deleting fewer than `k ≥ 2`
--   vertices contains a cycle.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L164-L204
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L164-L204

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.exists_cycArr_of_conn [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hn : 3 ≤ Fintype.card V) (hk2 : 2 ≤ k)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) :
    ∃ m f, CycArr G m f := by sorry
