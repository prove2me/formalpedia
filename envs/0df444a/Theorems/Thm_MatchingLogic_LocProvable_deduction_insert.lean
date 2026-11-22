-- Prove2me | Theorems.Thm_MatchingLogic_LocProvable_deduction_insert
-- name    : MatchingLogic.LocProvable.deduction_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:00.75119+00:00
-- url     : https://prove2.me/theorems/267caf8b-524c-4c5e-bf1c-aa5f6d4ada24
-- title:
--   Loc Provable: deduction insert
-- statement:
--   A single added local premise can be discharged inside the finite-premise
--   definition.  This is propositional only; it does not use the global deduction
--   theorem, which would be unsound for unrestricted quantifier generalisation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L327-L338
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L327-L338

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternLocalTheory
attribute [local instance] instDecidableEqPatternLocalTheory
open MatchingLogic.LocProvable

theorem MatchingLogic.LocProvable.deduction_insert {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (h : LocProvable (insert phi Gamma) psi) : LocProvable Gamma (.imp phi psi) := by sorry
