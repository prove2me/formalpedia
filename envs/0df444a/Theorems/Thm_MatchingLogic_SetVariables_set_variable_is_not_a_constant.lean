-- Prove2me | Theorems.Thm_MatchingLogic_SetVariables_set_variable_is_not_a_constant
-- name    : MatchingLogic.SetVariables.set_variable_is_not_a_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:57.181556+00:00
-- url     : https://prove2.me/theorems/47053680-1a81-426f-96a6-8d0c2a8c101d
-- title:
--   Set Variables: set variable is not a constant
-- statement:
--   **Remark 17.**  Reading a free set variable as a constant does not preserve
--   global consequence: the same `Γ ⊨ φ` is true on the left and false on the right.
--   So Corollary 15 does not extend to patterns with free set variables.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean#L128-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean#L128-L131

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

theorem MatchingLogic.SetVariables.set_variable_is_not_a_constant (X : SVar) :
    SGlobalCons (S := constSig) (Var := Var) {SPattern.svar X} SPattern.bot ∧
      ¬ GlobalCons (S := constSig) (Var := Var) {dPat} Pattern.bot := by sorry
