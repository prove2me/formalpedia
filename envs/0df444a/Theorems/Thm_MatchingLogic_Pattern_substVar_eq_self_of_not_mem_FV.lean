-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_substVar_eq_self_of_not_mem_FV
-- name    : MatchingLogic.Pattern.substVar_eq_self_of_not_mem_FV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:23.610318+00:00
-- url     : https://prove2.me/theorems/89dca746-06d2-43ab-8142-c0c4f7ba401b
-- title:
--   Pattern: subst Var eq self of not mem FV
-- statement:
--   Raw variable substitution is inert when its source variable is not free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Soundness.lean#L37-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Soundness.lean#L37-L63

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
attribute [local instance] Classical.propDecidable

theorem MatchingLogic.Pattern.substVar_eq_self_of_not_mem_FV {x y : Var} {φ : Pattern S Var}
    (hx : x ∉ FV φ) : substVar x y φ = φ := by sorry
