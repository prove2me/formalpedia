-- Prove2me | Theorems.Thm_MatchingLogic_FV_bot
-- name    : MatchingLogic.FV_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:43.409126+00:00
-- url     : https://prove2.me/theorems/0dc76a85-74a6-47f6-b776-35bfe9470825
-- title:
--   Matching Logic: FV bot
-- statement:
--   The Matching Logic construction uses the FV bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L45-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L45-L45

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

theorem MatchingLogic.FV_bot : FV (.bot : Pattern S Var) = ∅ := by sorry

attribute [defeq] MatchingLogic.FV_bot
