-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_mp_mem
-- name    : MatchingLogic.IsMCS.mp_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:04.209817+00:00
-- url     : https://prove2.me/theorems/9840a6fe-b42c-411c-8388-bc1042ddf0cf
-- title:
--   Is MCS: mp mem
-- statement:
--   Proposition 69(5).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L431-L435
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L431-L435

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

theorem MatchingLogic.IsMCS.mp_mem {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hM : IsMCS Gamma) (hphi : phi ∈ Gamma) (himp : Pattern.imp phi psi ∈ Gamma) :
    psi ∈ Gamma := by sorry
