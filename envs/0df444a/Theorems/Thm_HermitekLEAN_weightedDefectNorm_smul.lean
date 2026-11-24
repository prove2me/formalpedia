-- Prove2me | Theorems.Thm_HermitekLEAN_weightedDefectNorm_smul
-- name    : HermitekLEAN.weightedDefectNorm_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:30:12.95936+00:00
-- url     : https://prove2.me/theorems/cc3b943f-019a-411a-aa20-63f46a26eb7f
-- title:
--   Hermitek LEAN: weighted Defect Norm smul
-- statement:
--   Weighted defect norms are homogeneous under scalar multiplication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1717-L1741
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1717-L1741

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

theorem HermitekLEAN.weightedDefectNorm_smul (c : ℂ) (F0 G : ℂ → ℂ) :
    weightedDefectNorm (c • F0) (c • G) = ‖c‖ * weightedDefectNorm F0 G := by sorry
