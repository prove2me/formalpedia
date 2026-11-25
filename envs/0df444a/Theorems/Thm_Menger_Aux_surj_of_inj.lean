-- Prove2me | Theorems.Thm_Menger_Aux_surj_of_inj
-- name    : Menger.Aux.surj_of_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:44.677866+00:00
-- url     : https://prove2.me/theorems/208e9fcd-1e6f-4b97-8363-74105e0d9f78
-- title:
--   Aux: surj of inj
-- statement:
--   The Aux construction uses the surj of inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L204-L218
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L204-L218

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.surj_of_inj {k : ℕ} {X : Finset V} (f : Fin k → V) (hf : ∀ i, f i ∈ X)
    (hinj : Function.Injective f) (hc : X.card ≤ k) : ∀ v ∈ X, ∃ i, f i = v := by sorry
