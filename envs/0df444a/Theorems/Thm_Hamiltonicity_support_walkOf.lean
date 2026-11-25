-- Prove2me | Theorems.Thm_Hamiltonicity_support_walkOf
-- name    : Hamiltonicity.support_walkOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:35.962331+00:00
-- url     : https://prove2.me/theorems/3540ce6a-82e9-4247-8943-7af58ee59bfe
-- title:
--   Hamiltonicity: support walk Of
-- statement:
--   The Hamiltonicity construction uses the support walk Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L107-L114
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L107-L114

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.support_walkOf (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1)))
    (n : ℕ) : (walkOf G f hf n).support = (List.range (n + 1)).map f := by sorry
