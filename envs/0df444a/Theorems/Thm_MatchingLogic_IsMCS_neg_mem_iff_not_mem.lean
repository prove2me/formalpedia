-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_neg_mem_iff_not_mem
-- name    : MatchingLogic.IsMCS.neg_mem_iff_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:26.879824+00:00
-- url     : https://prove2.me/theorems/b4e9d45c-856a-4eff-a479-7709edc0b735
-- title:
--   Is MCS: neg mem iff not mem
-- statement:
--   Proposition 69(2): an MCS contains precisely one of a pattern and its
--   negation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L371-L378
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L371-L378

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

theorem MatchingLogic.IsMCS.neg_mem_iff_not_mem {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hM : IsMCS Gamma) : Pattern.nt phi ∈ Gamma ↔ phi ∉ Gamma := by sorry
