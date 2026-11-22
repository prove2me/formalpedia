-- Prove2me | Theorems.Thm_MatchingLogic_completedEmbed_injective
-- name    : MatchingLogic.completedEmbed_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:08.337799+00:00
-- url     : https://prove2.me/theorems/e1cbd2c0-a719-47c7-b560-7dda9cf32655
-- title:
--   Matching Logic: completed Embed injective
-- statement:
--   The generated-world embedding is injective.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L67-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L67-L71

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

theorem MatchingLogic.completedEmbed_injective (root : CanonicalCarrier S) :
    Function.Injective (completedEmbed root) := by sorry
