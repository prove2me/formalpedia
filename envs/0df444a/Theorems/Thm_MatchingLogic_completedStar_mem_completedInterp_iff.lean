-- Prove2me | Theorems.Thm_MatchingLogic_completedStar_mem_completedInterp_iff
-- name    : MatchingLogic.completedStar_mem_completedInterp_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:17.431366+00:00
-- url     : https://prove2.me/theorems/3b144b0d-253a-4965-a12f-cb06e6bbf03e
-- title:
--   Matching Logic: completed Star mem completed Interp iff
-- statement:
--   On all-real inputs, star is output exactly when one component is the
--   generated root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L196-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L196-L212

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

theorem MatchingLogic.completedStar_mem_completedInterp_iff
    {root : CanonicalCarrier S} (hmissing : Missing root) {sigma : S.Sym}
    (components : Fin (S.arity sigma) → GeneratedCarrier root) :
    completedStar hmissing ∈
        completedInterp root sigma (fun i => completedEmbed root (components i)) ↔
      ∃ i, components i = generatedRoot root := by sorry
