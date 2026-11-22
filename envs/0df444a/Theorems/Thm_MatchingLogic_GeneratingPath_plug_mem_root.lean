-- Prove2me | Theorems.Thm_MatchingLogic_GeneratingPath_plug_mem_root
-- name    : MatchingLogic.GeneratingPath.plug_mem_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:25.782883+00:00
-- url     : https://prove2.me/theorems/9eafd4b4-39e4-4702-8e7f-1e6e03712018
-- title:
--   Generating Path: plug mem root
-- statement:
--   Source Lemma 77: a generating context transports every member of its end
--   world back into the root MCS.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L207-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L207-L229

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

theorem MatchingLogic.GeneratingPath.plug_mem_root {root world : CanonicalCarrier S}
    {path : List (Coord S)} (hpath : GeneratingPath root world path)
    {p : Pattern S Nat} (hp : p ∈ (world : Set (Pattern S Nat))) :
    (generatingContext path).plug p ∈ (root : Set (Pattern S Nat)) := by sorry
