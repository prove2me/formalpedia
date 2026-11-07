-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_mapOut_eval
-- name    : NaturalProofs.MCircuit.mapOut_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:51.025119+00:00
-- url     : https://prove2.me/theorems/dd331d59-1888-41ed-b90b-e9cad73c2055
-- title:
--   MCircuit: map Out eval
-- statement:
--   The MCircuit construction uses the map Out eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L179-L180
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L179-L180

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.mapOut_eval (g : δ → γ) (C : MCircuit α γ) (x : α → Bool) (c : δ) :
    (C.mapOut g).eval x c = C.eval x (g c) := by sorry
