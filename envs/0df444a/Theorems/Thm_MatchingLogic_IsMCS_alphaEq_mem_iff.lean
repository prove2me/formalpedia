-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_alphaEq_mem_iff
-- name    : MatchingLogic.IsMCS.alphaEq_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:29.215993+00:00
-- url     : https://prove2.me/theorems/33eba253-77ce-458f-8c7d-2361b624a9f2
-- title:
--   Is MCS: alpha Eq mem iff
-- statement:
--   MCS membership is invariant under the kernel-level alpha-equivalence
--   relation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L67-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L67-L73

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

theorem MatchingLogic.IsMCS.alphaEq_mem_iff {Gamma : Set (Pattern S Nat)} {p q : Pattern S Nat}
    (hM : IsMCS Gamma) (halpha : Pattern.AlphaEq p q) : p ∈ Gamma ↔ q ∈ Gamma := by sorry
