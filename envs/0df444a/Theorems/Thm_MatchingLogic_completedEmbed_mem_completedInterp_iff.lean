-- Prove2me | Theorems.Thm_MatchingLogic_completedEmbed_mem_completedInterp_iff
-- name    : MatchingLogic.completedEmbed_mem_completedInterp_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:18.14246+00:00
-- url     : https://prove2.me/theorems/67cca73e-a13f-4894-b448-e944247161af
-- title:
--   Matching Logic: completed Embed mem completed Interp iff
-- statement:
--   On all-real inputs, real output membership is exactly membership in the
--   generated interpretation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L172-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L172-L192

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

theorem MatchingLogic.completedEmbed_mem_completedInterp_iff
    (root : CanonicalCarrier S) {sigma : S.Sym}
    (components : Fin (S.arity sigma) → GeneratedCarrier root)
    (world : GeneratedCarrier root) :
    completedEmbed root world ∈
        completedInterp root sigma (fun i => completedEmbed root (components i)) ↔
      world ∈ generatedInterp root sigma components := by sorry
