-- Prove2me | Theorems.Thm_MatchingLogic_GeneratingPath_generated
-- name    : MatchingLogic.GeneratingPath.generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:41.59549+00:00
-- url     : https://prove2.me/theorems/46a5f7e4-a0af-450c-a008-7474ff9da170
-- title:
--   Generating Path: generated
-- statement:
--   A source generating path witnesses membership in the reachability closure.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L184-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L184-L191

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

theorem MatchingLogic.GeneratingPath.generated {root world : CanonicalCarrier S}
    {path : List (Coord S)} (hpath : GeneratingPath root world path) :
    Generated root world := by sorry
