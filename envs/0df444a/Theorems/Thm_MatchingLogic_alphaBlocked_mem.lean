-- Prove2me | Theorems.Thm_MatchingLogic_alphaBlocked_mem
-- name    : MatchingLogic.alphaBlocked_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:25.468604+00:00
-- url     : https://prove2.me/theorems/4c8ebe0a-6aac-400b-a290-4e70b2503bc2
-- title:
--   Matching Logic: alpha Blocked mem
-- statement:
--   The Matching Logic construction uses the alpha Blocked mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L171-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L171-L179

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

theorem MatchingLogic.alphaBlocked_mem : alphaBlocked ∈ alphaWitnessTheory := by sorry
