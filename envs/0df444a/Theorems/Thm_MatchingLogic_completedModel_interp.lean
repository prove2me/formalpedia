-- Prove2me | Theorems.Thm_MatchingLogic_completedModel_interp
-- name    : MatchingLogic.completedModel_interp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:04.899897+00:00
-- url     : https://prove2.me/theorems/ffda6f3e-76be-46f3-94a7-33e464f10930
-- title:
--   Matching Logic: completed Model interp
-- statement:
--   The Matching Logic construction uses the completed Model interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L144-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L144-L148

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

theorem MatchingLogic.completedModel_interp (root : CanonicalCarrier S)
    (sigma : S.Sym)
    (inputs : Fin (S.arity sigma) → CompletedCarrier root) :
    (completedModel root).interp sigma inputs = completedInterp root sigma inputs := by sorry

attribute [defeq] MatchingLogic.completedModel_interp
