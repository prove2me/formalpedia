-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_mem_iff_locProvable
-- name    : MatchingLogic.IsMCS.mem_iff_locProvable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:05.536797+00:00
-- url     : https://prove2.me/theorems/6c7190a4-e506-425b-a8b0-aa725598e771
-- title:
--   Is MCS: mem iff loc Provable
-- statement:
--   Proposition 69(1): membership is exactly local derivability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L359-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L359-L367

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

theorem MatchingLogic.IsMCS.mem_iff_locProvable {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hM : IsMCS Gamma) : phi ∈ Gamma ↔ LocProvable Gamma phi := by sorry
