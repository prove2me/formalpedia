-- Prove2me | Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS
-- name    : MatchingLogic.CanonicalCarrier.isMCS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:04.758809+00:00
-- url     : https://prove2.me/theorems/b1220054-7da6-471a-855a-c2534ce88243
-- title:
--   Canonical Carrier: is MCS
-- statement:
--   The underlying theory of a canonical point is an MCS.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L55-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L55-L57

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

theorem MatchingLogic.CanonicalCarrier.isMCS (Gamma : CanonicalCarrier S) :
    IsMCS Gamma.val := by sorry
