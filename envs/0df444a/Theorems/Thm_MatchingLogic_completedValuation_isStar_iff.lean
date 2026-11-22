-- Prove2me | Theorems.Thm_MatchingLogic_completedValuation_isStar_iff
-- name    : MatchingLogic.completedValuation_isStar_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:26.591816+00:00
-- url     : https://prove2.me/theorems/172b6d54-f538-44ca-bcd7-3f70e079416c
-- title:
--   Matching Logic: completed Valuation is Star iff
-- statement:
--   The completed valuation is star exactly for variables missing from all
--   generated worlds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L228-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L228-L250

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCompletion

theorem MatchingLogic.completedValuation_isStar_iff (root : CanonicalCarrier S) (x : Nat) :
    (completedValuation root x).isStar ↔
      ∀ world : GeneratedCarrier root, Pattern.var x ∉ world.val.val := by sorry
