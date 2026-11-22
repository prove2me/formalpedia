-- Prove2me | Theorems.Thm_MatchingLogic_EntryIIIRegression_strong_completeness_has_nonempty_witness
-- name    : MatchingLogic.EntryIIIRegression.strong_completeness_has_nonempty_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:21.940895+00:00
-- url     : https://prove2.me/theorems/322be352-931d-4725-b7af-31b7f21ad170
-- title:
--   Entry IIIRegression: strong completeness has nonempty witness
-- statement:
--   Completeness at `{x} ⊨loc x` cannot escape via an empty finite witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L215-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Regression.lean#L215-L229

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

theorem MatchingLogic.EntryIIIRegression.strong_completeness_has_nonempty_witness :
    ∃ l : List (Pattern AuditSig Nat),
      l ≠ [] ∧
      (∀ delta ∈ l, delta ∈ ({(.var 0 : Pattern AuditSig Nat)} : Set _)) ∧
      Provable (∅ : Set (Pattern AuditSig Nat)) (.imp (conj l) (.var 0)) := by sorry
