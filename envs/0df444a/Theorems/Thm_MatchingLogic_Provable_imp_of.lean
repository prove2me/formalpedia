-- Prove2me | Theorems.Thm_MatchingLogic_Provable_imp_of
-- name    : MatchingLogic.Provable.imp_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:27.225326+00:00
-- url     : https://prove2.me/theorems/d36b173e-c53d-4b64-b9f5-4598fa175a0a
-- title:
--   Provable: imp of
-- statement:
--   A theorem remains derivable under an arbitrary antecedent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L70-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L70-L74

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

theorem MatchingLogic.Provable.imp_of {Gamma : Set (Pattern S Var)}
    {phi psi : Pattern S Var} (h : Provable Gamma phi) : Provable Gamma (.imp psi phi) := by sorry
