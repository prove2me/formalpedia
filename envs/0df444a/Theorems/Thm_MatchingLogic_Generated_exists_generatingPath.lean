-- Prove2me | Theorems.Thm_MatchingLogic_Generated_exists_generatingPath
-- name    : MatchingLogic.Generated.exists_generatingPath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:27.254897+00:00
-- url     : https://prove2.me/theorems/4792a194-eb99-48f2-bdeb-5426a3476c60
-- title:
--   Generated: exists generating Path
-- statement:
--   Reachability and the paper's explicit generating-path relation agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L194-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L194-L203

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

theorem MatchingLogic.Generated.exists_generatingPath {root world : CanonicalCarrier S}
    (hgen : Generated root world) :
    ∃ path : List (Coord S), GeneratingPath root world path := by sorry
