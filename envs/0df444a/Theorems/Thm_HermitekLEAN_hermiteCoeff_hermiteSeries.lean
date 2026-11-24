-- Prove2me | Theorems.Thm_HermitekLEAN_hermiteCoeff_hermiteSeries
-- name    : HermitekLEAN.hermiteCoeff_hermiteSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:27.668686+00:00
-- url     : https://prove2.me/theorems/273472d6-a274-48b5-a126-6c61dc369750
-- title:
--   Hermitek LEAN: hermite Coeff hermite Series
-- statement:
--   Fourier inversion: the canonical coefficients of a Hermite series recover
--       the original coefficient sequence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L4098-L4112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L4098-L4112

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

theorem HermitekLEAN.hermiteCoeff_hermiteSeries :
    ∀ {k : ℕ} {G : ℂ → ℂ} (h : ℕ → ℂ),
      G ∈ Hk k →
      G = hermiteSeries k h →
      Summable (fun n => ‖h n‖ ^ 2) →
      (∀ n, hermiteCoeff k G n = h n) := by sorry
