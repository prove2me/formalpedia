-- Prove2me | Theorems.Thm_MatchingLogic_Generated_exists_generatingContext
-- name    : MatchingLogic.Generated.exists_generatingContext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:29.769315+00:00
-- url     : https://prove2.me/theorems/765ac217-9aee-47df-a8e5-8587f39e0659
-- title:
--   Generated: exists generating Context
-- statement:
--   Every reachable world has a context transporting all of its members into
--   the root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L233-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L233-L239

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

theorem MatchingLogic.Generated.exists_generatingContext {root world : CanonicalCarrier S}
    (hgen : Generated root world) :
    ∃ C : AppCtx S Nat,
      ∀ p ∈ (world : Set (Pattern S Nat)),
        C.plug p ∈ (root : Set (Pattern S Nat)) := by sorry
