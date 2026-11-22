-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_and_mem_iff
-- name    : MatchingLogic.IsMCS.and_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:43.235624+00:00
-- url     : https://prove2.me/theorems/a2771074-6dcf-442e-ac50-075aa907f769
-- title:
--   Is MCS: and mem iff
-- statement:
--   Proposition 69(3), binary case.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L381-L394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L381-L394

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
open MatchingLogic.IsMCS

theorem MatchingLogic.IsMCS.and_mem_iff {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hM : IsMCS Gamma) : Pattern.and phi psi ∈ Gamma ↔ phi ∈ Gamma ∧ psi ∈ Gamma := by sorry
