-- Prove2me | Theorems.Thm_MatchingLogic_exists_completedStar_iff_missing
-- name    : MatchingLogic.exists_completedStar_iff_missing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:49.327553+00:00
-- url     : https://prove2.me/theorems/283ce395-fd55-4526-8fbd-89f14b5e8f89
-- title:
--   Matching Logic: exists completed Star iff missing
-- statement:
--   The representation has a star point exactly in the source's
--   missing-variable case.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L83-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L83-L89

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

theorem MatchingLogic.exists_completedStar_iff_missing (root : CanonicalCarrier S) :
    (∃ point : CompletedCarrier root, point.isStar) ↔ Missing root := by sorry
