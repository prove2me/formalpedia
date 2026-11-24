-- Prove2me | Theorems.Thm_HermitekLEAN_hermiteCoeff_truncate
-- name    : HermitekLEAN.hermiteCoeff_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:14.84607+00:00
-- url     : https://prove2.me/theorems/614b4975-9185-4cf9-a921-1ac1b7e9d54d
-- title:
--   Hermitek LEAN: hermite Coeff truncate
-- statement:
--   The truncation keeps exactly the first `J + 1` Hermite coefficients.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1871-L1877
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1871-L1877

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

theorem HermitekLEAN.hermiteCoeff_truncate :
    ∀ {k J : ℕ} {G : ℂ → ℂ} (n : ℕ),
      hermiteCoeff k (truncate k J G) n =
        if _h : n < J + 1 then hermiteCoeff k G n else 0 := by sorry
