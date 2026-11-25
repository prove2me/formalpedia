-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_ne_succ
-- name    : Hamiltonicity.CycArr.ne_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:16:42.245651+00:00
-- url     : https://prove2.me/theorems/2a3e2639-d1d1-4e27-95d8-ef49372a178e
-- title:
--   Cyc Arr: ne succ
-- statement:
--   The Cyc Arr construction uses the ne succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L28-L38
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L28-L38

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.CycArr.ne_succ {G : SimpleGraph V} {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) (i : ℕ) :
    f i ≠ f (i + 1) := by sorry
