-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_FV_subset_allVars
-- name    : MatchingLogic.Pattern.FV_subset_allVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:24.205731+00:00
-- url     : https://prove2.me/theorems/10451aec-7f70-4600-b31a-84176b364912
-- title:
--   Pattern: FV subset all Vars
-- statement:
--   Every free variable occurs in the finite set of all variable names.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Fresh.lean#L42-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Fresh.lean#L42-L58

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

theorem MatchingLogic.Pattern.FV_subset_allVars (p : Pattern S Var) : FV p ⊆ ↑p.allVars := by sorry
