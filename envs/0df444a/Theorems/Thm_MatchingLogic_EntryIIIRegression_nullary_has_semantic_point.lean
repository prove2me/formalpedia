-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_nullary_has_semantic_point
-- name    : MatchingLogic.EntryIIIRegression.nullary_has_semantic_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:05.228451+00:00
-- url     : https://prove2.me/theorems/14e8dd9f-8763-40db-8458-4f8f12fa29b4
-- title:
--   Entry IIIRegression: nullary has semantic point
-- statement:
--   The Entry IIIRegression construction uses the nullary has semantic point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L182-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L182-L185

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

theorem MatchingLogic.EntryIIIRegression.nullary_has_semantic_point :
    false ∈ auditModel.denoteSet auditRho
      ({nullaryPattern} : Set (Pattern AuditSig Nat)) := by sorry
