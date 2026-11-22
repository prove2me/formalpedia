-- Prove2me | Theorems.Thm_MatchingLogic_CanonicalCarrier_witnessed
-- name    : MatchingLogic.CanonicalCarrier.witnessed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:59.750701+00:00
-- url     : https://prove2.me/theorems/42255c53-a968-4b40-9a81-1b957a06d322
-- title:
--   Canonical Carrier: witnessed
-- statement:
--   Forgetting freshness recovers the interface used by the basic Truth Lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L65-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L65-L67

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
open MatchingLogic.CanonicalCarrier

theorem MatchingLogic.CanonicalCarrier.witnessed (Gamma : CanonicalCarrier S) :
    Witnessed Gamma.val := by sorry
