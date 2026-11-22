-- Prove2me | Theorems.Thm_MatchingLogic_mem_completedModel_interp
-- name    : MatchingLogic.mem_completedModel_interp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:05.290974+00:00
-- url     : https://prove2.me/theorems/0fe0e35e-da3d-449a-b3f8-22e69454ed8a
-- title:
--   Matching Logic: mem completed Model interp
-- statement:
--   The Matching Logic construction uses the mem completed Model interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L150-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L150-L155

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

theorem MatchingLogic.mem_completedModel_interp {root : CanonicalCarrier S}
    {sigma : S.Sym} {inputs : Fin (S.arity sigma) → CompletedCarrier root}
    {output : CompletedCarrier root} :
    output ∈ (completedModel root).interp sigma inputs ↔
      output ∈ completedInterp root sigma inputs := by sorry
