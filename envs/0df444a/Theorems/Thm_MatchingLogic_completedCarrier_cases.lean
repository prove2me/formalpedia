-- Prove2me | Theorems.Thm_MatchingLogic_completedCarrier_cases
-- name    : MatchingLogic.completedCarrier_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:23.748809+00:00
-- url     : https://prove2.me/theorems/aa639755-9643-4db9-94c9-090c5b060426
-- title:
--   Matching Logic: completed Carrier cases
-- statement:
--   Every completed point is either an embedded generated world or the unique
--   conditional star.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L93-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L93-L108

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

theorem MatchingLogic.completedCarrier_cases {root : CanonicalCarrier S}
    (point : CompletedCarrier root) :
    (∃ world : GeneratedCarrier root, point = completedEmbed root world) ∨
      (∃ hmissing : Missing root, point = completedStar hmissing) := by sorry
