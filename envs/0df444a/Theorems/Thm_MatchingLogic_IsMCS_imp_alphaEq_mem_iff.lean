-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_imp_alphaEq_mem_iff
-- name    : MatchingLogic.IsMCS.imp_alphaEq_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:14.942417+00:00
-- url     : https://prove2.me/theorems/65ff56e0-2753-48ac-bf6d-bbf8d66f2d05
-- title:
--   Is MCS: imp alpha Eq mem iff
-- statement:
--   Alpha-congruent implications have identical MCS membership.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L76-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L76-L80

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

theorem MatchingLogic.IsMCS.imp_alphaEq_mem_iff {Gamma : Set (Pattern S Nat)}
    {p p' q q' : Pattern S Nat} (hM : IsMCS Gamma)
    (hp : Pattern.AlphaEq p p') (hq : Pattern.AlphaEq q q') :
    Pattern.imp p q ∈ Gamma ↔ Pattern.imp p' q' ∈ Gamma := by sorry
