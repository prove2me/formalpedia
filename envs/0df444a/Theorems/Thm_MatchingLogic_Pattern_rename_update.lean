-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_rename_update
-- name    : MatchingLogic.Pattern.rename_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:26.344803+00:00
-- url     : https://prove2.me/theorems/8ef61f09-38ae-4cc2-b44a-19627f94e70b
-- title:
--   Pattern: rename update
-- statement:
--   Renaming a tuple commutes with replacing one argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L150-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L150-L158

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

theorem MatchingLogic.Pattern.rename_update (f : Var → Var') {n : Nat}
    (args : Fin n → Pattern S Var) (i : Fin n) (p : Pattern S Var) :
    (fun j => (Function.update args i p j).rename f) =
      Function.update (fun j => (args j).rename f) i (p.rename f) := by sorry
