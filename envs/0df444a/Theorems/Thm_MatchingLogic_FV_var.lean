-- Prove2me | Theorems.Thm_MatchingLogic_FV_var
-- name    : MatchingLogic.FV_var
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:43.285579+00:00
-- url     : https://prove2.me/theorems/50497fa6-b2a8-4b79-a0a5-28c124dfa203
-- title:
--   Matching Logic: FV var
-- statement:
--   The Matching Logic construction uses the FV var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L43-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L43-L43

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]

theorem MatchingLogic.FV_var (x : Var) : FV (.var x : Pattern S Var) = {x} := by sorry

attribute [defeq] MatchingLogic.FV_var
