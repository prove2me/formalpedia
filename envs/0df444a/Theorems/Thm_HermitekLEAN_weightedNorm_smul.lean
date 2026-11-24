-- Prove2me | Theorems.Thm_HermitekLEAN_weightedNorm_smul
-- name    : HermitekLEAN.weightedNorm_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:30:04.136477+00:00
-- url     : https://prove2.me/theorems/c5c5f0ec-75ac-4f5d-b3ba-9a77d565242f
-- title:
--   Hermitek LEAN: weighted Norm smul
-- statement:
--   Weighted norms are homogeneous under scalar multiplication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1700-L1714
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1700-L1714

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

theorem HermitekLEAN.weightedNorm_smul (c : ℂ) (G : ℂ → ℂ) :
    weightedNorm (c • G) = ‖c‖ * weightedNorm G := by sorry
