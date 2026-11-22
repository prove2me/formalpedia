-- Prove2me | Theorems.Thm_MatchingLogic_completedValuation_surjective
-- name    : MatchingLogic.completedValuation_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:28.556851+00:00
-- url     : https://prove2.me/theorems/c6a33fe5-5437-4140-9937-17ebca9cd16f
-- title:
--   Matching Logic: completed Valuation surjective
-- statement:
--   Every point of the completed carrier is named by some element variable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L282-L294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L282-L294

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

theorem MatchingLogic.completedValuation_surjective (root : CanonicalCarrier S) :
    Function.Surjective (completedValuation root) := by sorry
