-- Prove2me | Theorems.Thm_MatchingLogic_SetVariables_sGlobalCons_svar_bot
-- name    : MatchingLogic.SetVariables.sGlobalCons_svar_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:18.082156+00:00
-- url     : https://prove2.me/theorems/862ceff5-c57b-4bf4-a5a2-d78cb8a3a3c3
-- title:
--   Set Variables: s Global Cons svar bot
-- statement:
--   Hence `{X} ⊨ ⊥` holds **vacuously**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean#L94-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean#L94-L97

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_SetVariables
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.SetVariables
variable {S : Signature} {Var SVar : Type} [DecidableEq Var]

theorem MatchingLogic.SetVariables.sGlobalCons_svar_bot (X : SVar) :
    SGlobalCons (S := S) (Var := Var) {SPattern.svar X} SPattern.bot := by sorry
