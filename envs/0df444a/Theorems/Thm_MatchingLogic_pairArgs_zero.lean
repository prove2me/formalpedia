-- Prove2me | Theorems.Thm_MatchingLogic_pairArgs_zero
-- name    : MatchingLogic.pairArgs_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:50.9085+00:00
-- url     : https://prove2.me/theorems/f3748702-139b-43a1-90eb-93645180dc42
-- title:
--   Matching Logic: pair Args zero
-- statement:
--   The Matching Logic construction uses the pair Args zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L127-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L127-L128

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

theorem MatchingLogic.pairArgs_zero (p q : Pattern AlphaWitnessSig Nat) :
    pairArgs p q 0 = p := by sorry

attribute [defeq] MatchingLogic.pairArgs_zero
