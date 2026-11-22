-- Prove2me | Theorems.Thm_MatchingLogic_CanonicalCarrier_top_mem
-- name    : MatchingLogic.CanonicalCarrier.top_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:42.549709+00:00
-- url     : https://prove2.me/theorems/c24a1b65-a528-4c44-b12b-9c03904fb6c1
-- title:
--   Canonical Carrier: top mem
-- statement:
--   Every canonical MCS contains `top`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L178-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L178-L181

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

theorem MatchingLogic.CanonicalCarrier.top_mem (world : CanonicalCarrier S) :
    (Pattern.tp : Pattern S Nat) ∈ (world : Set (Pattern S Nat)) := by sorry
