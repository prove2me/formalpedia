-- Prove2me | Theorems.Thm_MatchingLogic_SetVariables_not_ssat_svar
-- name    : MatchingLogic.SetVariables.not_ssat_svar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:11.545807+00:00
-- url     : https://prove2.me/theorems/5bf20a03-8c73-4823-8dbd-5768ac22f64a
-- title:
--   Set Variables: not ssat svar
-- statement:
--   **No model satisfies a bare set variable**, because the valuation sending it
--   to `∅` makes it not total.  This is the step a constant does not admit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean#L84-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SetVariables.lean#L84-L91

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

theorem MatchingLogic.SetVariables.not_ssat_svar (M : Model S) (X : SVar) :
    ¬ SSat (Var := Var) M (.svar X) := by sorry
