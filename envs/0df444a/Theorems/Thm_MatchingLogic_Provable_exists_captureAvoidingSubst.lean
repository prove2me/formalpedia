-- Prove2me | Theorems.Thm_MatchingLogic_Provable_exists_captureAvoidingSubst
-- name    : MatchingLogic.Provable.exists_captureAvoidingSubst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:17.120538+00:00
-- url     : https://prove2.me/theorems/2836d5f9-3a28-42c1-bb73-fbf6c8285ef7
-- title:
--   Provable: exists capture Avoiding Subst
-- statement:
--   The source's alpha-renaming fact with its actual side condition: `y` need
--   only be absent from the free variables of `p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L151-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L151-L164

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

theorem MatchingLogic.Provable.exists_captureAvoidingSubst {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ FV p) :
    Provable Gamma (.imp (.ex x p)
      (.ex y (Pattern.captureAvoidingSubst x y p))) := by sorry
