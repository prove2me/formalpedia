-- Prove2me | Theorems.Thm_MatchingLogic_mem_completedInterp
-- name    : MatchingLogic.mem_completedInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:44.606679+00:00
-- url     : https://prove2.me/theorems/ba0dd5d2-3fcf-416c-a5f7-a181fba42c14
-- title:
--   Matching Logic: mem completed Interp
-- statement:
--   The Matching Logic construction uses the mem completed Interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L132-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L132-L142

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

theorem MatchingLogic.mem_completedInterp {root : CanonicalCarrier S} {sigma : S.Sym}
    {inputs : Fin (S.arity sigma) → CompletedCarrier root}
    {output : CompletedCarrier root} :
    output ∈ completedInterp root sigma inputs ↔
      ∃ components : Fin (S.arity sigma) → GeneratedCarrier root,
        (∀ i, inputs i = completedEmbed root (components i)) ∧
          ((∃ world : GeneratedCarrier root,
              output = completedEmbed root world ∧
                world ∈ generatedInterp root sigma components) ∨
           (output.isStar ∧ ∃ i, components i = generatedRoot root)) := by sorry
