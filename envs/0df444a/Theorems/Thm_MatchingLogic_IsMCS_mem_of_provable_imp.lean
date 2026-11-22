-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_imp
-- name    : MatchingLogic.IsMCS.mem_of_provable_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:19.447827+00:00
-- url     : https://prove2.me/theorems/c306555a-4522-4815-a6a8-dbedb8496a7d
-- title:
--   Is MCS: mem of provable imp
-- statement:
--   MCS membership transports along an empty-theory implication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L38-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L38-L41

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS

theorem MatchingLogic.IsMCS.mem_of_provable_imp {Gamma : Set (Pattern S Nat)} {p q : Pattern S Nat}
    (hM : IsMCS Gamma) (hp : p ∈ Gamma)
    (hpq : Provable (∅ : Set (Pattern S Nat)) (.imp p q)) : q ∈ Gamma := by sorry
