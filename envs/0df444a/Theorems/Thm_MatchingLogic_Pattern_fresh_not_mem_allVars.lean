-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_fresh_not_mem_allVars
-- name    : MatchingLogic.Pattern.fresh_not_mem_allVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:24.105198+00:00
-- url     : https://prove2.me/theorems/68c2bc5a-773c-4f5f-b3cf-49ad1885c2cb
-- title:
--   Pattern: fresh not mem all Vars
-- statement:
--   The canonical fresh name does not occur free or bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Fresh.lean#L65-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Fresh.lean#L65-L70

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.fresh_not_mem_allVars (p : Pattern S Nat) : p.fresh ∉ p.allVars := by sorry
