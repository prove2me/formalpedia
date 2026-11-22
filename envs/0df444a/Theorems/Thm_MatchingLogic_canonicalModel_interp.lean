-- Prove2me | Theorems.Thm_MatchingLogic_canonicalModel_interp
-- name    : MatchingLogic.canonicalModel_interp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:00.662643+00:00
-- url     : https://prove2.me/theorems/3b11b1c7-7411-42f9-b0ae-1abc455b0f01
-- title:
--   Matching Logic: canonical Model interp
-- statement:
--   The Matching Logic construction uses the canonical Model interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L115-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L115-L118

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore

theorem MatchingLogic.canonicalModel_interp (root : CanonicalCarrier S)
    (sigma : S.Sym) (components : Fin (S.arity sigma) → CanonicalCarrier S) :
    (canonicalModel root).interp sigma components = canonicalInterp sigma components := by sorry

attribute [defeq] MatchingLogic.canonicalModel_interp
