-- Prove2me | Theorems.Thm_MatchingLogic_strongLocalCompleteness_congr
-- name    : MatchingLogic.strongLocalCompleteness_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:56.788109+00:00
-- url     : https://prove2.me/theorems/974f87f3-dd35-4e8c-aa07-8f5aed6d2226
-- title:
--   Matching Logic: strong Local Completeness congr
-- statement:
--   Strong local completeness depends only on the variable type up to equivalence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L351-L382
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L351-L382

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.strongLocalCompleteness_congr [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') :
    StrongLocalCompleteness S Var ↔ StrongLocalCompleteness S Var' := by sorry
