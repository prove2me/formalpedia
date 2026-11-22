-- Prove2me | Theorems.Thm_MatchingLogic_LocProvable_of_mem
-- name    : MatchingLogic.LocProvable.of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:01.574869+00:00
-- url     : https://prove2.me/theorems/b5e9e2e5-46e7-431a-9bb2-19fa286607be
-- title:
--   Loc Provable: of mem
-- statement:
--   The Loc Provable construction uses the of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L247-L253
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L247-L253

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

theorem MatchingLogic.LocProvable.of_mem {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : phi ∈ Gamma) : LocProvable Gamma phi := by sorry
