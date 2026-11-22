-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_mem_FV_renameEquiv
-- name    : MatchingLogic.Pattern.mem_FV_renameEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:55.165789+00:00
-- url     : https://prove2.me/theorems/7b3fa157-8c23-45e4-a2d4-febe8cbc14a2
-- title:
--   Pattern: mem FV rename Equiv
-- statement:
--   Free-variable membership commutes with a bijective renaming.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L88-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L88-L91

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

theorem MatchingLogic.Pattern.mem_FV_renameEquiv
    (e : Var ≃ Var') (p : Pattern S Var) (y : Var') :
    y ∈ FV (p.rename e) ↔ e.symm y ∈ FV p := by sorry
