-- Prove2me | Theorems.Thm_HermitekLEAN_finiteHermiteSum_mem_Hk
-- name    : HermitekLEAN.finiteHermiteSum_mem_Hk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:16.324875+00:00
-- url     : https://prove2.me/theorems/9ba9ade8-38eb-425a-b554-edb919d906d3
-- title:
--   Hermitek LEAN: finite Hermite Sum mem Hk
-- statement:
--   Every finite Hermite sum belongs to the true level space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1767-L1805
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1767-L1805

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN

theorem HermitekLEAN.finiteHermiteSum_mem_Hk :
    ∀ (k : ℕ) {D : ℕ} (a : Fin D → ℂ), finiteHermiteSum k a ∈ Hk k := by sorry
