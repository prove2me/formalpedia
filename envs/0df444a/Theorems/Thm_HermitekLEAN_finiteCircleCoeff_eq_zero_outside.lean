-- Prove2me | Theorems.Thm_HermitekLEAN_finiteCircleCoeff_eq_zero_outside
-- name    : HermitekLEAN.finiteCircleCoeff_eq_zero_outside
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:30:14.213816+00:00
-- url     : https://prove2.me/theorems/cb2216d7-a8e8-46a5-a877-c0b6d8b1fd29
-- title:
--   Hermitek LEAN: finite Circle Coeff eq zero outside
-- statement:
--   The finite circle coefficient map vanishes outside the finite frequency range.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2009-L2014
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2009-L2014

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

theorem HermitekLEAN.finiteCircleCoeff_eq_zero_outside :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ) {n : ℕ},
      D ≤ n →
        finiteCircleCoeff k r a n = 0 := by sorry
