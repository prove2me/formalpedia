-- Prove2me | Theorems.Thm_MatchingLogic_Provable_imp_exists_to_exists_imp
-- name    : MatchingLogic.Provable.imp_exists_to_exists_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:01.279933+00:00
-- url     : https://prove2.me/theorems/140d18e0-911e-448c-ac31-d66f424d1932
-- title:
--   Provable: imp exists to exists imp
-- statement:
--   Predicate-logic choice in the exact form needed by Lemma 80.  Nonemptiness
--   is supplied proof-theoretically by existential introduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L188-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L188-L215

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

theorem MatchingLogic.Provable.imp_exists_to_exists_imp {Gamma : Set (Pattern S Nat)}
    {y : Nat} {a q : Pattern S Nat} :
    Provable Gamma (.imp (.imp a (.ex y q)) (.ex y (.imp a q))) := by sorry
