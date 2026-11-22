-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_imp_mem_iff
-- name    : MatchingLogic.IsMCS.imp_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:10.531151+00:00
-- url     : https://prove2.me/theorems/ebd28011-9133-4d17-97e0-d896a855e016
-- title:
--   Is MCS: imp mem iff
-- statement:
--   Boolean membership clause for primitive implication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L114-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L114-L134

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

theorem MatchingLogic.IsMCS.imp_mem_iff {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma)
    (p q : Pattern S Nat) :
    Pattern.imp p q ∈ Gamma ↔ p ∉ Gamma ∨ q ∈ Gamma := by sorry
