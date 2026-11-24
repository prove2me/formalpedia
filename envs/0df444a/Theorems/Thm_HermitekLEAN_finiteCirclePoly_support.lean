-- Prove2me | Theorems.Thm_HermitekLEAN_finiteCirclePoly_support
-- name    : HermitekLEAN.finiteCirclePoly_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:30:16.842585+00:00
-- url     : https://prove2.me/theorems/fff6dd65-60f5-4c8c-9925-c6459effff12
-- title:
--   Hermitek LEAN: finite Circle Poly support
-- statement:
--   The finite circle polynomial is supported in frequencies `{0, ..., D - 1}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2017-L2022
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2017-L2022

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

theorem HermitekLEAN.finiteCirclePoly_support :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ),
      finiteCirclePoly k r a =
        positiveTrigonometricPolynomial (frequencyBand 0 D) (finiteCircleCoeff k r a) := by sorry
