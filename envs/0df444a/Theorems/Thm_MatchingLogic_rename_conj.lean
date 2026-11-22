-- Prove2me | Theorems.Thm_MatchingLogic_rename_conj
-- name    : MatchingLogic.rename_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:28.870075+00:00
-- url     : https://prove2.me/theorems/39a1dbac-dea3-4566-b5dc-335b043d679d
-- title:
--   Matching Logic: rename conj
-- statement:
--   Renaming distributes through finite conjunction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L198-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L198-L202

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.rename_conj (f : Var → Var') (l : List (Pattern S Var)) :
    (conj l).rename f = conj (l.map (Pattern.rename f)) := by sorry
