-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_conj_mem_iff
-- name    : MatchingLogic.IsMCS.conj_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:31.116342+00:00
-- url     : https://prove2.me/theorems/e148ba34-bfd9-4fc6-b510-ab033a3ea2e6
-- title:
--   Is MCS: conj mem iff
-- statement:
--   Proposition 69(3), for the repository's finite-list conjunction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L397-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L397-L403

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

theorem MatchingLogic.IsMCS.conj_mem_iff {Gamma : Set (Pattern S Var)} (hM : IsMCS Gamma)
    (l : List (Pattern S Var)) : conj l ∈ Gamma ↔ ∀ phi ∈ l, phi ∈ Gamma := by sorry
