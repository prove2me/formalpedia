-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_freshTuple_injective
-- name    : MatchingLogic.Pattern.freshTuple_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:11.957806+00:00
-- url     : https://prove2.me/theorems/47ae74c4-89d5-4d94-a723-21c0288ee1dd
-- title:
--   Pattern: fresh Tuple injective
-- statement:
--   The Pattern construction uses the fresh Tuple injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L92-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalExistence.lean#L92-L97

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.freshTuple_injective (p : Pattern S Nat) (Phi : Fin n → Pattern S Nat) :
    Function.Injective (freshTuple p Phi) := by sorry
