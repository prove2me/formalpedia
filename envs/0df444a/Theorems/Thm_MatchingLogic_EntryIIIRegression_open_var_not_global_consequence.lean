-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_open_var_not_global_consequence
-- name    : MatchingLogic.EntryIIIRegression.open_var_not_global_consequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:41.460237+00:00
-- url     : https://prove2.me/theorems/077e5313-b8b4-464b-ab1b-8bf106748eaf
-- title:
--   Entry IIIRegression: open var not global consequence
-- statement:
--   An open variable is not a semantic consequence of the empty theory.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L84-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L84-L91

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

theorem MatchingLogic.EntryIIIRegression.open_var_not_global_consequence :
    ¬ GlobalCons (∅ : Set (Pattern AuditSig Nat))
      (.var 0 : Pattern AuditSig Nat) := by sorry
