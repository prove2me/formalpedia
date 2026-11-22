-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_canonical_existence_unary_branch
-- name    : MatchingLogic.EntryIIIRegression.canonical_existence_unary_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:21.737836+00:00
-- url     : https://prove2.me/theorems/ca25afc2-6bbf-4511-ae3f-5cf332f41641
-- title:
--   Entry IIIRegression: canonical existence unary branch
-- statement:
--   The Entry IIIRegression construction uses the canonical existence unary branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L283-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L283-L289

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Regression
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set
attribute [local instance] MatchingLogic.EntryIIIRegression.instEncodableAuditSym
attribute [local instance] MatchingLogic.EntryIIIRegression.auditPatternCountable

theorem MatchingLogic.EntryIIIRegression.canonical_existence_unary_branch
    (Gamma : CanonicalCarrier AuditSig)
    (happ : unaryPattern ∈ Gamma.val) :
    ∃ components : Fin (AuditSig.arity AuditSym.unary) → CanonicalCarrier AuditSig,
      (∀ i, (Pattern.var 0 : Pattern AuditSig Nat) ∈ (components i).val) ∧
      Gamma ∈ canonicalInterp AuditSym.unary components := by sorry
