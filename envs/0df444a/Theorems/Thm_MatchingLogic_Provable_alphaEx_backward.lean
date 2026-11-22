-- Prove2me | Theorems.Thm_MatchingLogic_Provable_alphaEx_backward
-- name    : MatchingLogic.Provable.alphaEx_backward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:30.005862+00:00
-- url     : https://prove2.me/theorems/d279414e-9870-492c-9d87-dc39aa07eed2
-- title:
--   Provable: alpha Ex backward
-- statement:
--   Derived backward alpha conversion for an existential binder.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L177-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L177-L182

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.Provable.alphaEx_backward {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ p.allVars) :
    Provable Gamma (.imp (.ex y (substVar x y p)) (.ex x p)) := by sorry
