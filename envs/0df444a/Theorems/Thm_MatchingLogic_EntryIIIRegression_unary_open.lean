-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_unary_open
-- name    : MatchingLogic.EntryIIIRegression.unary_open
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:59.263807+00:00
-- url     : https://prove2.me/theorems/e7d1b285-0c00-481d-9cdd-f7dcacacbab0
-- title:
--   Entry IIIRegression: unary open
-- statement:
--   The Entry IIIRegression construction uses the unary open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L141-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L141-L144

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

theorem MatchingLogic.EntryIIIRegression.unary_open : ¬ Closed unaryPattern := by sorry
