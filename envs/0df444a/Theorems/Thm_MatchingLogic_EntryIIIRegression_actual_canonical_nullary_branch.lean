-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_actual_canonical_nullary_branch
-- name    : MatchingLogic.EntryIIIRegression.actual_canonical_nullary_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:42.330078+00:00
-- url     : https://prove2.me/theorems/e1922dc1-592e-4b4c-ba87-c6f537df70ee
-- title:
--   Entry IIIRegression: actual canonical nullary branch
-- statement:
--   The nullary canonical-existence branch is invoked from an inhabited MCS premise.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L292-L307
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L292-L307

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

theorem MatchingLogic.EntryIIIRegression.actual_canonical_nullary_branch :
    ∃ root : CanonicalCarrier AuditSig,
      ∃ components : Fin (AuditSig.arity AuditSym.nullary) →
          CanonicalCarrier AuditSig,
        root ∈ canonicalInterp AuditSym.nullary components := by sorry
