-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_bot_not_empty_theorem
-- name    : MatchingLogic.EntryIIIRegression.bot_not_empty_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:50.400809+00:00
-- url     : https://prove2.me/theorems/70c17823-bf58-43bd-9929-e8dd4515df9f
-- title:
--   Entry IIIRegression: bot not empty theorem
-- statement:
--   Soundness transfers the explicit bottom countermodel to non-provability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L94-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L94-L97

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

theorem MatchingLogic.EntryIIIRegression.bot_not_empty_theorem :
    ¬ Provable (∅ : Set (Pattern AuditSig Nat)) .bot := by sorry
