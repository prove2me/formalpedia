-- Prove2me | Theorems.Thm_MatchingLogic_strongLocalCompleteness_iff_nat
-- name    : MatchingLogic.strongLocalCompleteness_iff_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:59.961293+00:00
-- url     : https://prove2.me/theorems/316b9f32-8d55-42e5-a573-edbee7976d8a
-- title:
--   Matching Logic: strong Local Completeness iff nat
-- statement:
--   A source-faithful countably infinite variable type can be reduced to `Nat`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L385-L387
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L385-L387

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.strongLocalCompleteness_iff_nat [DecidableEq Var] [Denumerable Var] :
    StrongLocalCompleteness S Var ↔ StrongLocalCompleteness S Nat := by sorry
