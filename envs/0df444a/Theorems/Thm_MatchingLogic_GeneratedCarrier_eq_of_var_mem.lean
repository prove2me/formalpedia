-- Prove2me | Theorems.Thm_MatchingLogic_GeneratedCarrier_eq_of_var_mem
-- name    : MatchingLogic.GeneratedCarrier.eq_of_var_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:29.382256+00:00
-- url     : https://prove2.me/theorems/cdcebd0d-17fa-4576-9ea6-4f73c2d35aa4
-- title:
--   Generated Carrier: eq of var mem
-- statement:
--   Carrier form of Singleton Variables, used by the later completed
--   valuation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L293-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L293-L299

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated

theorem MatchingLogic.GeneratedCarrier.eq_of_var_mem {root : CanonicalCarrier S}
    (left right : GeneratedCarrier root) {x : Nat}
    (hxleft : Pattern.var x ∈ left.val.val)
    (hxright : Pattern.var x ∈ right.val.val) :
    left = right := by sorry
