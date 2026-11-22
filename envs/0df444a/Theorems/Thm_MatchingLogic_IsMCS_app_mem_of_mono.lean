-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_app_mem_of_mono
-- name    : MatchingLogic.IsMCS.app_mem_of_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:16.129157+00:00
-- url     : https://prove2.me/theorems/9456a7d2-4781-42fb-a61a-1a7cc2ec21b4
-- title:
--   Is MCS: app mem of mono
-- statement:
--   Membership transport through pointwise application monotonicity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L59-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L59-L63

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

theorem MatchingLogic.IsMCS.app_mem_of_mono {Gamma : Set (Pattern S Nat)} {sigma : S.Sym}
    {args args' : Fin (S.arity sigma) → Pattern S Nat} (hM : IsMCS Gamma)
    (hargs : ∀ i, Provable (∅ : Set (Pattern S Nat)) (.imp (args i) (args' i)))
    (hmem : Pattern.app sigma args ∈ Gamma) : Pattern.app sigma args' ∈ Gamma := by sorry
