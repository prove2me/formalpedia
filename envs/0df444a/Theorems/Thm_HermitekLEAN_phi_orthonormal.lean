-- Prove2me | Theorems.Thm_HermitekLEAN_phi_orthonormal
-- name    : HermitekLEAN.phi_orthonormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:40.681691+00:00
-- url     : https://prove2.me/theorems/13c66408-047d-448b-b38c-c7f8d6f03a77
-- title:
--   Hermitek LEAN: phi orthonormal
-- statement:
--   The level-`k` basis is orthonormal for the weighted inner product.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1171-L1251
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1171-L1251

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

theorem HermitekLEAN.phi_orthonormal :
    ∀ {k m n : ℕ},
      weightedInner (Phi k m) (Phi k n) = if m = n then 1 else 0 := by sorry
