-- Prove2me | Theorems.Thm_MatchingLogic_LocProvable_provable_empty
-- name    : MatchingLogic.LocProvable.provable_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:21.490922+00:00
-- url     : https://prove2.me/theorems/ab2cd14a-ed1c-45a2-b25b-33f967a492f7
-- title:
--   Loc Provable: provable empty
-- statement:
--   With no local premises, local derivability collapses to ordinary
--   empty-theory provability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L133-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L133-L143

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore

theorem MatchingLogic.LocProvable.provable_empty {p : Pattern S Nat}
    (h : LocProvable (∅ : Set (Pattern S Nat)) p) :
    Provable (∅ : Set (Pattern S Nat)) p := by sorry
