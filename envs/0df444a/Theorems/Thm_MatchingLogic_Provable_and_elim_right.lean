-- Prove2me | Theorems.Thm_MatchingLogic_Provable_and_elim_right
-- name    : MatchingLogic.Provable.and_elim_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:56.975833+00:00
-- url     : https://prove2.me/theorems/0bfe743b-78b5-4409-9d60-5055b735b941
-- title:
--   Provable: and elim right
-- statement:
--   Right conjunction elimination.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L94-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L94-L98

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

theorem MatchingLogic.Provable.and_elim_right (Gamma : Set (Pattern S Var)) (phi psi : Pattern S Var) :
    Provable Gamma (.imp (Pattern.and phi psi) psi) := by sorry
