-- Prove2me | Theorems.Thm_Hamiltonicity_edges_walkOf
-- name    : Hamiltonicity.edges_walkOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:55.552226+00:00
-- url     : https://prove2.me/theorems/10e11011-c9ed-512e-b4d5-540676489b6d
-- title:
--   Hamiltonicity: edges walk Of
-- statement:
--   The Hamiltonicity construction uses the edges walk Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L116-L123
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L116-L123

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.edges_walkOf (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1)))
    (n : ℕ) : (walkOf G f hf n).edges = (List.range n).map (fun i => s(f i, f (i + 1))) := by sorry
