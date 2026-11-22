-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_mem_FV_rename_injective
-- name    : MatchingLogic.Pattern.mem_FV_rename_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:40.830629+00:00
-- url     : https://prove2.me/theorems/143a2fa5-7c1f-4485-b6ab-1815bc563f89
-- title:
--   Pattern: mem FV rename injective
-- statement:
--   Free-variable membership is reflected at an embedded variable name.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L68-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L68-L85

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.mem_FV_rename_injective
    (f : Var → Var') (hf : Function.Injective f) (p : Pattern S Var) (x : Var) :
    f x ∈ FV (p.rename f) ↔ x ∈ FV p := by sorry
