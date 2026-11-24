-- Prove2me | Theorems.Thm_HermitekLEAN_orthogonal_phi0_iff_hermiteCoeff_zero
-- name    : HermitekLEAN.orthogonal_phi0_iff_hermiteCoeff_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:25.138967+00:00
-- url     : https://prove2.me/theorems/1dc5be96-0772-4e06-b428-23b5652892e5
-- title:
--   Hermitek LEAN: orthogonal phi0 iff hermite Coeff zero
-- statement:
--   Orthogonality to `Phi k 0` is equivalent to vanishing zeroth Hermite coefficient.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1850-L1852
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1850-L1852

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

theorem HermitekLEAN.orthogonal_phi0_iff_hermiteCoeff_zero :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      weightedInner G (phi0 k) = 0 ↔ hermiteCoeff k G 0 = 0 := by sorry
