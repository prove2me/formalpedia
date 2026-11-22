-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_canonical_existence_nullary_branch
-- name    : MatchingLogic.EntryIIIRegression.canonical_existence_nullary_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:04.059621+00:00
-- url     : https://prove2.me/theorems/e2bc9153-203a-47e6-849c-1076d15cf4ed
-- title:
--   Entry IIIRegression: canonical existence nullary branch
-- statement:
--   The Entry IIIRegression construction uses the canonical existence nullary branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L274-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L274-L281

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

theorem MatchingLogic.EntryIIIRegression.canonical_existence_nullary_branch
    (Gamma : CanonicalCarrier AuditSig)
    (happ : nullaryPattern ∈ Gamma.val) :
    ∃ components : Fin (AuditSig.arity AuditSym.nullary) → CanonicalCarrier AuditSig,
      (∀ i, (fun j : Fin (AuditSig.arity AuditSym.nullary) => Fin.elim0 j) i ∈
        (components i).val) ∧
      Gamma ∈ canonicalInterp AuditSym.nullary components := by sorry
