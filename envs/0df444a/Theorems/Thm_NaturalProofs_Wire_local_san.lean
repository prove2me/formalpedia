-- Prove2me | Theorems.Thm_NaturalProofs_Wire_local_san
-- name    : NaturalProofs.Wire.local_san
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:59.694134+00:00
-- url     : https://prove2.me/theorems/196db155-7825-49d7-8cb8-0b694ed61d3d
-- title:
--   Wire: local san
-- statement:
--   The Wire construction uses the local san property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L77-L80
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L77-L80

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.Wire.local_san (n : ℕ) (w : Wire β) : (w.san n).Local n := by sorry
