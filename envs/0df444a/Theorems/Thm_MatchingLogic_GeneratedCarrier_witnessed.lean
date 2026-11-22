-- Prove2me | Theorems.Thm_MatchingLogic_GeneratedCarrier_witnessed
-- name    : MatchingLogic.GeneratedCarrier.witnessed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:41.442727+00:00
-- url     : https://prove2.me/theorems/3d782904-faac-4d20-b156-1234275d0e6d
-- title:
--   Generated Carrier: witnessed
-- statement:
--   A generated point still carries its canonical witnessedness proof.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L95-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L95-L97

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_witnessed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
open MatchingLogic.GeneratedCarrier

theorem MatchingLogic.GeneratedCarrier.witnessed {root : CanonicalCarrier S} (world : GeneratedCarrier root) :
    Witnessed world.val.val := by sorry
