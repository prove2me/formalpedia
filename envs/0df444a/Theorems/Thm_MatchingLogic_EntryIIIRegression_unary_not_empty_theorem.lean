-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_unary_not_empty_theorem
-- name    : MatchingLogic.EntryIIIRegression.unary_not_empty_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:12.483829+00:00
-- url     : https://prove2.me/theorems/d3978645-ee43-468f-8b2d-4c1288bbd16c
-- title:
--   Entry IIIRegression: unary not empty theorem
-- statement:
--   A unary application of an open variable is likewise not theoremhood.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L147-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L147-L156

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

theorem MatchingLogic.EntryIIIRegression.unary_not_empty_theorem :
    ¬ Provable (∅ : Set (Pattern AuditSig Nat)) unaryPattern := by sorry
