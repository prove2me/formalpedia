-- Prove2me | Theorems.Thm_MatchingLogic_pairArgs_one
-- name    : MatchingLogic.pairArgs_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:41:29.455316+00:00
-- url     : https://prove2.me/theorems/a7ca23e4-7b8c-4222-9e5b-02e180fee724
-- title:
--   Matching Logic: pair Args one
-- statement:
--   The Matching Logic construction uses the pair Args one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L130-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L130-L131

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section

theorem MatchingLogic.pairArgs_one (p q : Pattern AlphaWitnessSig Nat) :
    pairArgs p q 1 = q := by sorry

attribute [defeq] MatchingLogic.pairArgs_one
