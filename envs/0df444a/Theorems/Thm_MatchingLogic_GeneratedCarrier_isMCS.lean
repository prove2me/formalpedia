-- Prove2me | Theorems.Thm_MatchingLogic_GeneratedCarrier_isMCS
-- name    : MatchingLogic.GeneratedCarrier.isMCS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:29.62027+00:00
-- url     : https://prove2.me/theorems/96ad3b96-c8b1-4431-b353-6863d7cf2670
-- title:
--   Generated Carrier: is MCS
-- statement:
--   A generated point still carries its canonical MCS proof.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L90-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L90-L92

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
open MatchingLogic.GeneratedCarrier

theorem MatchingLogic.GeneratedCarrier.isMCS {root : CanonicalCarrier S} (world : GeneratedCarrier root) :
    IsMCS world.val.val := by sorry
