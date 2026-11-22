-- Prove2me | Theorems.Thm_MatchingLogic_generatedModel_interp
-- name    : MatchingLogic.generatedModel_interp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:24.775943+00:00
-- url     : https://prove2.me/theorems/93d934e1-8840-4909-affa-895966ed61c0
-- title:
--   Matching Logic: generated Model interp
-- statement:
--   The Matching Logic construction uses the generated Model interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L124-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L124-L129

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated

theorem MatchingLogic.generatedModel_interp (root : CanonicalCarrier S)
    (sigma : S.Sym)
    (components : Fin (S.arity sigma) → GeneratedCarrier root) :
    (generatedModel root).interp sigma components =
      generatedInterp root sigma components := by sorry

attribute [defeq] MatchingLogic.generatedModel_interp
