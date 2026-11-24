-- Prove2me | Theorems.Thm_HermitekLEAN_circleSeries_fourierCoeff_hermiteCoeff
-- name    : HermitekLEAN.circleSeries_fourierCoeff_hermiteCoeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:47.283403+00:00
-- url     : https://prove2.me/theorems/4a5648ea-4cbf-4da4-b506-9e0d43715023
-- title:
--   Hermitek LEAN: circle Series fourier Coeff hermite Coeff
-- statement:
--   The canonical circle series has the expected Fourier coefficients.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3377-L3455
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3377-L3455

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

theorem HermitekLEAN.circleSeries_fourierCoeff_hermiteCoeff :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ {r : ℝ}, 0 < r →
          ∀ n : ℕ,
            fourierCoeff (circleSeries k (hermiteCoeff k G) r) (n : ℤ) =
              hermiteCoeff k G n * (qkn k n r : ℂ) := by sorry
