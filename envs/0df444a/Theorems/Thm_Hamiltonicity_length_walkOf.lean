-- Prove2me | Theorems.Thm_Hamiltonicity_length_walkOf
-- name    : Hamiltonicity.length_walkOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:39.027475+00:00
-- url     : https://prove2.me/theorems/d1a484a8-eee9-485e-970a-cad1b565c04e
-- title:
--   Hamiltonicity: length walk Of
-- statement:
--   The Hamiltonicity construction uses the length walk Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L125-L129
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L125-L129

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.length_walkOf (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1)))
    (n : ℕ) : (walkOf G f hf n).length = n := by sorry
