-- Prove2me | Theorems.Thm_MatchingLogic_completedStar_ne_embed
-- name    : MatchingLogic.completedStar_ne_embed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:20.400894+00:00
-- url     : https://prove2.me/theorems/61983045-95af-4a28-ac67-c8d6d4a55bb6
-- title:
--   Matching Logic: completed Star ne embed
-- statement:
--   The conditional star is distinct from every embedded generated world.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L74-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L74-L79

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

theorem MatchingLogic.completedStar_ne_embed {root : CanonicalCarrier S}
    (hmissing : Missing root) (world : GeneratedCarrier root) :
    completedStar hmissing ≠ completedEmbed root world := by sorry
