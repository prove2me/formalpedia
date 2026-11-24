-- Prove2me | Theorems.Thm_HermitekLEAN_truncate_eq_finiteHermiteSum
-- name    : HermitekLEAN.truncate_eq_finiteHermiteSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:43.187276+00:00
-- url     : https://prove2.me/theorems/e3d6e9c6-9099-4ab5-9df1-d5f5bfb85907
-- title:
--   Hermitek LEAN: truncate eq finite Hermite Sum
-- statement:
--   The truncation operator is the explicit finite Hermite sum of the first coefficients.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1855-L1860
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1855-L1860

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

theorem HermitekLEAN.truncate_eq_finiteHermiteSum :
    ∀ {k J : ℕ} {G : ℂ → ℂ},
      truncate k J G =
        finiteHermiteSum k (fun n : Fin (J + 1) => hermiteCoeff k G n.1) := by sorry
