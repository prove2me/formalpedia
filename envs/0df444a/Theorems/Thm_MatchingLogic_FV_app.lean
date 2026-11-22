-- Prove2me | Theorems.Thm_MatchingLogic_FV_app
-- name    : MatchingLogic.FV_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:48.379923+00:00
-- url     : https://prove2.me/theorems/332f75a3-29e9-487b-855c-388c82b6a09f
-- title:
--   Matching Logic: FV app
-- statement:
--   The Matching Logic construction uses the FV app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L49-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L49-L50

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

theorem MatchingLogic.FV_app (σ : S.Sym) (f : Fin (S.arity σ) → Pattern S Var) :
    FV (.app σ f) = ⋃ i, FV (f i) := by sorry

attribute [defeq] MatchingLogic.FV_app
