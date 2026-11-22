-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_fresh_not_mem_FV
-- name    : MatchingLogic.Pattern.fresh_not_mem_FV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:43.652449+00:00
-- url     : https://prove2.me/theorems/b633eb45-1138-4eef-b988-6fd31758e9ac
-- title:
--   Pattern: fresh not mem FV
-- statement:
--   In particular, the canonical fresh name is not free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Fresh.lean#L73-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Fresh.lean#L73-L75

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

theorem MatchingLogic.Pattern.fresh_not_mem_FV (p : Pattern S Nat) : p.fresh ∉ FV p := by sorry
