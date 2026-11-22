-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_comp_eq_of_fresh_result
-- name    : MatchingLogic.Pattern.captureAvoidingSubst_comp_eq_of_fresh_result
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:36.631687+00:00
-- url     : https://prove2.me/theorems/63bc2410-2e82-475e-90ca-d95a4fff66ba
-- title:
--   Pattern: capture Avoiding Subst comp eq of fresh result
-- statement:
--   Exact composition when the result name is fresh for the current body.
--   The `z = y` case is an inert self-substitution; otherwise support tracking
--   shows that the second capture-avoidance pass is a raw substitution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean#L108-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FreshWitnessElim.lean#L108-L122

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.captureAvoidingSubst_comp_eq_of_fresh_result {x y z : Nat}
    {p : Pattern S Nat} (hy : y ∉ p.allVars) (hz : z ∉ p.allVars)
    (hzs : z ∉ (substVar x y p).allVars) :
    captureAvoidingSubst y z (captureAvoidingSubst x y p) =
      captureAvoidingSubst x z p := by sorry
