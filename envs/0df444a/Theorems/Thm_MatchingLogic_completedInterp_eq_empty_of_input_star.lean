-- Prove2me | Theorems.Thm_MatchingLogic_completedInterp_eq_empty_of_input_star
-- name    : MatchingLogic.completedInterp_eq_empty_of_input_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:08.263073+00:00
-- url     : https://prove2.me/theorems/0bc5f27e-4560-4147-adcc-179c40fac15e
-- title:
--   Matching Logic: completed Interp eq empty of input star
-- statement:
--   Any star input forces the completed symbol interpretation to be empty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L158-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L158-L168

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCompletion

theorem MatchingLogic.completedInterp_eq_empty_of_input_star {root : CanonicalCarrier S}
    {sigma : S.Sym} {inputs : Fin (S.arity sigma) → CompletedCarrier root}
    (i : Fin (S.arity sigma)) (hstar : (inputs i).isStar) :
    completedInterp root sigma inputs = ∅ := by sorry
