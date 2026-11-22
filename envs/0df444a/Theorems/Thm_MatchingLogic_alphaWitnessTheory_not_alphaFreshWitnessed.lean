-- Prove2me | Theorems.Thm_MatchingLogic_alphaWitnessTheory_not_alphaFreshWitnessed
-- name    : MatchingLogic.alphaWitnessTheory_not_alphaFreshWitnessed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:04.544839+00:00
-- url     : https://prove2.me/theorems/09bd072e-9168-4f10-bfb8-564d39aa413f
-- title:
--   Matching Logic: alpha Witness Theory not alpha Fresh Witnessed
-- statement:
--   No proof-theoretic alpha variant of `alphaBlocked` has a fresh usable
--   witness in the pointed binary model.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L457-L489
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L457-L489

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

theorem MatchingLogic.alphaWitnessTheory_not_alphaFreshWitnessed :
    ¬ AlphaFreshWitnessed alphaWitnessTheory := by sorry
