-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_substVar_eq_self_of_not_mem_allVars
-- name    : MatchingLogic.Pattern.substVar_eq_self_of_not_mem_allVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:59.929832+00:00
-- url     : https://prove2.me/theorems/16ae2e64-267f-41bc-bf29-775d28fe1777
-- title:
--   Pattern: subst Var eq self of not mem all Vars
-- statement:
--   Substitution does nothing when its source name occurs neither free nor bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L33-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L33-L52

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.substVar_eq_self_of_not_mem_allVars {x y : Nat} {p : Pattern S Nat}
    (hx : x ∉ p.allVars) : substVar x y p = p := by sorry
