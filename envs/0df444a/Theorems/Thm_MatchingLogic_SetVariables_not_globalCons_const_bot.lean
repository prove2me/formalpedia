-- Prove2me | Theorems.Thm_MatchingLogic_SetVariables_not_globalCons_const_bot
-- name    : MatchingLogic.SetVariables.not_globalCons_const_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:21.130344+00:00
-- url     : https://prove2.me/theorems/e71e41c7-40e3-46fe-bdb0-0fba2b0ae9ce
-- title:
--   Set Variables: not global Cons const bot
-- statement:
--   **But `{d} ⊭ ⊥`**, as the model with `d_M = M` shows.  So replacing the set
--   variable by a constant changes the truth of the consequence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean#L111-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean#L111-L123

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

theorem MatchingLogic.SetVariables.not_globalCons_const_bot :
    ¬ GlobalCons (S := constSig) (Var := Var) {dPat} Pattern.bot := by sorry
