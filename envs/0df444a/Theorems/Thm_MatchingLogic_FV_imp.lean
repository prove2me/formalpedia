-- Prove2me | Theorems.Thm_MatchingLogic_FV_imp
-- name    : MatchingLogic.FV_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:44.842592+00:00
-- url     : https://prove2.me/theorems/18b50121-dd1f-4e3d-9a73-dfe18e72ce8a
-- title:
--   Matching Logic: FV imp
-- statement:
--   The Matching Logic construction uses the FV imp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L47-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L47-L47

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

theorem MatchingLogic.FV_imp (φ ψ : Pattern S Var) : FV (.imp φ ψ) = FV φ ∪ FV ψ := by sorry

attribute [defeq] MatchingLogic.FV_imp
