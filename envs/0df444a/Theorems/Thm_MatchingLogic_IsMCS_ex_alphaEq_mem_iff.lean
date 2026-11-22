-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_ex_alphaEq_mem_iff
-- name    : MatchingLogic.IsMCS.ex_alphaEq_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:20.934867+00:00
-- url     : https://prove2.me/theorems/43eee8c7-a67d-4a3c-a75b-67319f41c9e6
-- title:
--   Is MCS: ex alpha Eq mem iff
-- statement:
--   Alpha-congruent existential bodies have identical MCS membership.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L83-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L83-L86

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

theorem MatchingLogic.IsMCS.ex_alphaEq_mem_iff {Gamma : Set (Pattern S Nat)} {x : Nat}
    {p q : Pattern S Nat} (hM : IsMCS Gamma) (h : Pattern.AlphaEq p q) :
    Pattern.ex x p ∈ Gamma ↔ Pattern.ex x q ∈ Gamma := by sorry
