-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_not_mem_FV_of_ne
-- name    : MatchingLogic.Pattern.captureAvoidingSubst_not_mem_FV_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:07.383847+00:00
-- url     : https://prove2.me/theorems/6b45d576-6f4b-418c-bd76-b588e4cd6d82
-- title:
--   Pattern: capture Avoiding Subst not mem FV of ne
-- statement:
--   A name distinct from the replacement and absent free from the source stays
--   absent free after total capture-avoiding substitution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L142-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L142-L145

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.captureAvoidingSubst_not_mem_FV_of_ne {x y z : Nat}
    {p : Pattern S Nat} (hzy : z ≠ y) (hzp : z ∉ FV p) :
    z ∉ FV (captureAvoidingSubst x y p) := by sorry
