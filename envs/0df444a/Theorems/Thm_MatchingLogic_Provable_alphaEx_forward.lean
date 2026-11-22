-- Prove2me | Theorems.Thm_MatchingLogic_Provable_alphaEx_forward
-- name    : MatchingLogic.Provable.alphaEx_forward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:01.603182+00:00
-- url     : https://prove2.me/theorems/7cdaa09d-6ac4-4d32-9545-c41291bb4f63
-- title:
--   Provable: alpha Ex forward
-- statement:
--   Derived forward alpha conversion for an existential binder.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L162-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L162-L174

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.Provable.alphaEx_forward {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ p.allVars) :
    Provable Gamma (.imp (.ex x p) (.ex y (substVar x y p))) := by sorry
