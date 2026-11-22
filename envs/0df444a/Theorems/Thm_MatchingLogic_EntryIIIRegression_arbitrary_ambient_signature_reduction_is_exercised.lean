-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_arbitrary_ambient_signature_reduction_is_exercised
-- name    : MatchingLogic.EntryIIIRegression.arbitrary_ambient_signature_reduction_is_exercised
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:46.225525+00:00
-- url     : https://prove2.me/theorems/c1a2eeaf-233d-4d7c-98f5-323574149702
-- title:
--   Entry IIIRegression: arbitrary ambient signature reduction is exercised
-- statement:
--   The finite-support reduction reaches the unconditional ambient result.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L350-L353
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L350-L353

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

theorem MatchingLogic.EntryIIIRegression.arbitrary_ambient_signature_reduction_is_exercised :
    FiniteLocalModelExistence HugeSig Nat ∧
      StrongLocalCompleteness HugeSig Nat := by sorry
