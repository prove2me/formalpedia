-- Prove2me | Theorems.Thm_MatchingLogic_alphaWitnessTheory_witnessed
-- name    : MatchingLogic.alphaWitnessTheory_witnessed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:41:40.986167+00:00
-- url     : https://prove2.me/theorems/13a1011d-fc74-4e5f-926c-2b17b435c9fd
-- title:
--   Matching Logic: alpha Witness Theory witnessed
-- statement:
--   The Matching Logic construction uses the alpha Witness Theory witnessed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L163-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L163-L165

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

theorem MatchingLogic.alphaWitnessTheory_witnessed : Witnessed alphaWitnessTheory := by sorry
