-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_ex_mem_of_mono
-- name    : MatchingLogic.IsMCS.ex_mem_of_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:00.742567+00:00
-- url     : https://prove2.me/theorems/a85f653d-aead-4d62-87b5-9585bf55d495
-- title:
--   Is MCS: ex mem of mono
-- statement:
--   Membership transport through existential monotonicity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L52-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/MCSAlpha.lean#L52-L56

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

theorem MatchingLogic.IsMCS.ex_mem_of_mono {Gamma : Set (Pattern S Nat)} {x : Nat}
    {p q : Pattern S Nat} (hM : IsMCS Gamma)
    (hpq : Provable (∅ : Set (Pattern S Nat)) (.imp p q))
    (hmem : Pattern.ex x p ∈ Gamma) : Pattern.ex x q ∈ Gamma := by sorry
