-- Prove2me | Theorems.Thm_MatchingLogic_Provable_witnessPushArg
-- name    : MatchingLogic.Provable.witnessPushArg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:38.399748+00:00
-- url     : https://prove2.me/theorems/0927a840-e789-41c3-a4a3-2242c031b29e
-- title:
--   Provable: witness Push Arg
-- statement:
--   One argument of Lemma 80, before application-context propagation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L293-L318
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L293-L318

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

theorem MatchingLogic.Provable.witnessPushArg {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {phi Phi : Pattern S Nat}
    (hyphi : y ∉ FV phi) (hyPhi : y ∉ FV Phi) :
    Provable Gamma (.imp Phi
      (.ex y (Pattern.and Phi
        (.imp (.ex x phi) (Pattern.captureAvoidingSubst x y phi))))) := by sorry
