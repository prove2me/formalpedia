-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_bot_not_mem
-- name    : MatchingLogic.IsMCS.bot_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:10.915501+00:00
-- url     : https://prove2.me/theorems/1830eadc-06c2-4d53-a4da-fb3775ac2691
-- title:
--   Is MCS: bot not mem
-- statement:
--   Bottom belongs to no maximal locally consistent set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L97-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L97-L100

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.IsMCS

theorem MatchingLogic.IsMCS.bot_not_mem {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma) :
    (.bot : Pattern S Nat) ∉ Gamma := by sorry
