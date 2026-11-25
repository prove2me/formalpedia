-- Prove2me | Theorems.Thm_Hamiltonicity_exists_cycArr_of_path
-- name    : Hamiltonicity.exists_cycArr_of_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:50.383974+00:00
-- url     : https://prove2.me/theorems/f12fed92-1a1a-5b10-8d1d-6b65bdc8128e
-- title:
--   Hamiltonicity: exists cyc Arr of path
-- statement:
--   A Hamiltonian path `x 0, …, x (n - 1)` whose ends have degree sum at least `n` can be closed
--   into a Hamiltonian cycle.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ClosureAux.lean#L28-L144
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ClosureAux.lean#L28-L144

module
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Definitions.Def_MengerHamilton_ClosureAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.exists_cycArr_of_path [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : ℕ → V) (hn : 3 ≤ Fintype.card V)
    (hinj : ∀ i j, i < Fintype.card V → j < Fintype.card V → x i = x j → i = j)
    (hadj : ∀ i, i + 1 < Fintype.card V → G.Adj (x i) (x (i + 1)))
    (hdeg : Fintype.card V ≤ G.degree (x 0) + G.degree (x (Fintype.card V - 1))) :
    ∃ g, CycArr G (Fintype.card V) g := by sorry
