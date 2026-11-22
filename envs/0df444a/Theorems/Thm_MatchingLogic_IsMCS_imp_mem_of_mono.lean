-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_imp_mem_of_mono
-- name    : MatchingLogic.IsMCS.imp_mem_of_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:01.885682+00:00
-- url     : https://prove2.me/theorems/fb5e05f1-1915-46d7-aad2-aaf28cd6a0f7
-- title:
--   Is MCS: imp mem of mono
-- statement:
--   Membership transport through implication monotonicity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L44-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L44-L49

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

theorem MatchingLogic.IsMCS.imp_mem_of_mono {Gamma : Set (Pattern S Nat)}
    {p p' q q' : Pattern S Nat} (hM : IsMCS Gamma)
    (hp : Provable (∅ : Set (Pattern S Nat)) (.imp p' p))
    (hq : Provable (∅ : Set (Pattern S Nat)) (.imp q q'))
    (hmem : Pattern.imp p q ∈ Gamma) : Pattern.imp p' q' ∈ Gamma := by sorry
