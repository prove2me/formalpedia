-- Prove2me | Theorems.Thm_HermitekLEAN_truncate_mem_Hk
-- name    : HermitekLEAN.truncate_mem_Hk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:05.853847+00:00
-- url     : https://prove2.me/theorems/80d3a422-6ad9-4552-a34f-44136d9f810c
-- title:
--   Hermitek LEAN: truncate mem Hk
-- statement:
--   Every truncation lies in the true level space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1944-L1948
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1944-L1948

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

theorem HermitekLEAN.truncate_mem_Hk :
    ∀ (k J : ℕ) (G : ℂ → ℂ), truncate k J G ∈ Hk k := by sorry
