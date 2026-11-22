-- Prove2me | Theorems.Thm_MatchingLogic_Provable_and_exists
-- name    : MatchingLogic.Provable.and_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:11.097234+00:00
-- url     : https://prove2.me/theorems/3e35c3ad-4829-4561-8f7c-e32626395364
-- title:
--   Provable: and exists
-- statement:
--   Move an existential through a conjunction whose other conjunct is fresh.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L245-L282
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L245-L282

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

theorem MatchingLogic.Provable.and_exists {Gamma : Set (Pattern S Nat)} {y : Nat}
    {p q : Pattern S Nat} (hy : y ∉ FV p) :
    Provable Gamma (.imp (Pattern.and p (.ex y q))
      (.ex y (Pattern.and p q))) := by sorry
