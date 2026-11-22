-- Prove2me | Theorems.Thm_MatchingLogic_Provable_imp_trans
-- name    : MatchingLogic.Provable.imp_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:14.682484+00:00
-- url     : https://prove2.me/theorems/52bd313b-f3df-4cc9-bc6d-beb8e93105d3
-- title:
--   Provable: imp trans
-- statement:
--   Transitivity of implication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L55-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L55-L62

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

theorem MatchingLogic.Provable.imp_trans {Gamma : Set (Pattern S Var)}
    {phi psi chi : Pattern S Var} (h1 : Provable Gamma (.imp phi psi))
    (h2 : Provable Gamma (.imp psi chi)) : Provable Gamma (.imp phi chi) := by sorry
