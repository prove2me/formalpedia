-- Prove2me | Theorems.Thm_MatchingLogic_generated_singleton_variables
-- name    : MatchingLogic.generated_singleton_variables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:36.273622+00:00
-- url     : https://prove2.me/theorems/5c0ad665-2cb7-4dbc-a451-484d07d9f8e7
-- title:
--   Matching Logic: generated singleton variables
-- statement:
--   Source Lemma 78: a variable pattern belongs to at most one reachable
--   canonical world.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L278-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L278-L289

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated

theorem MatchingLogic.generated_singleton_variables (root : CanonicalCarrier S)
    {left right : CanonicalCarrier S}
    (hleft : Generated root left) (hright : Generated root right)
    {x : Nat} (hxleft : Pattern.var x ∈ (left : Set (Pattern S Nat)))
    (hxright : Pattern.var x ∈ (right : Set (Pattern S Nat))) :
    left = right := by sorry
