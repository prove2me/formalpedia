-- Prove2me | Theorems.Thm_MatchingLogic_CanonicalCarrier_exists_var_mem
-- name    : MatchingLogic.CanonicalCarrier.exists_var_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:18.072285+00:00
-- url     : https://prove2.me/theorems/1ca5076e-2c05-4db4-a98b-a68a4e06015d
-- title:
--   Canonical Carrier: exists var mem
-- statement:
--   Carrier-specialized form of variable existence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L84-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L84-L87

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore

theorem MatchingLogic.CanonicalCarrier.exists_var_mem (Gamma : CanonicalCarrier S) :
    ∃ y : Nat, Pattern.var y ∈ Gamma.val := by sorry
