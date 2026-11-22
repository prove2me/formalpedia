-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_empty
-- name    : MatchingLogic.IsMCS.mem_of_provable_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:27.424472+00:00
-- url     : https://prove2.me/theorems/9167dde1-6f35-4ac7-917d-e74dec6467da
-- title:
--   Is MCS: mem of provable empty
-- statement:
--   Every empty-theory theorem belongs to every MCS.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L33-L35
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L33-L35

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

theorem MatchingLogic.IsMCS.mem_of_provable_empty {Gamma : Set (Pattern S Nat)} {p : Pattern S Nat}
    (hM : IsMCS Gamma) (h : Provable (∅ : Set (Pattern S Nat)) p) : p ∈ Gamma := by sorry
