-- Prove2me | Theorems.Thm_MatchingLogic_FV_ex
-- name    : MatchingLogic.FV_ex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:47.203133+00:00
-- url     : https://prove2.me/theorems/6850c597-7993-426f-a5ff-db1da2308c8d
-- title:
--   Matching Logic: FV ex
-- statement:
--   The Matching Logic construction uses the FV ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L52-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L52-L52

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

theorem MatchingLogic.FV_ex (x : Var) (φ : Pattern S Var) : FV (.ex x φ) = FV φ \ {x} := by sorry

attribute [defeq] MatchingLogic.FV_ex
