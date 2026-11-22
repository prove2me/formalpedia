-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_global_completeness_bottom_both_false
-- name    : MatchingLogic.EntryIIIRegression.global_completeness_bottom_both_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:14.383733+00:00
-- url     : https://prove2.me/theorems/88cbbe66-06e5-40ec-96b0-ea469678dc91
-- title:
--   Entry IIIRegression: global completeness bottom both false
-- statement:
--   At bottom, the final global-completeness equivalence relates two false sides.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L106-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L106-L122

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

theorem MatchingLogic.EntryIIIRegression.global_completeness_bottom_both_false :
    (¬ GlobalCons (∅ : Set (Pattern AuditSig Nat))
      (.bot : Pattern AuditSig Nat)) ∧
    (¬ Provable (∅ : Set (Pattern AuditSig Nat))
      (.bot : Pattern AuditSig Nat)) ∧
    (GlobalCons (∅ : Set (Pattern AuditSig Nat))
        (.bot : Pattern AuditSig Nat) ↔
      Provable (∅ : Set (Pattern AuditSig Nat))
        (.bot : Pattern AuditSig Nat)) := by sorry
