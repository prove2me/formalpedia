-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_comp_alphaEq
-- name    : MatchingLogic.Pattern.captureAvoidingSubst_comp_alphaEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:15.63591+00:00
-- url     : https://prove2.me/theorems/51556f31-dbcd-4291-acd3-a46f078af177
-- title:
--   Pattern: capture Avoiding Subst comp alpha Eq
-- statement:
--   Source substitution composition modulo alpha equivalence.  The intermediate
--   name is fresh only from free variables; the final name is arbitrary.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessElim.lean#L425-L454
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessElim.lean#L425-L454

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessElim
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.captureAvoidingSubst_comp_alphaEq {x y z : Nat}
    {p : Pattern S Nat} (hy : y ∉ FV p) :
    AlphaEq
      (captureAvoidingSubst y z (captureAvoidingSubst x y p))
      (captureAvoidingSubst x z p) := by sorry
