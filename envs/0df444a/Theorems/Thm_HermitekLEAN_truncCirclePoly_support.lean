-- Prove2me | Theorems.Thm_HermitekLEAN_truncCirclePoly_support
-- name    : HermitekLEAN.truncCirclePoly_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:30:29.603995+00:00
-- url     : https://prove2.me/theorems/8361fecb-b41c-4ce1-9151-64ca5f0df8ca
-- title:
--   Hermitek LEAN: trunc Circle Poly support
-- statement:
--   The truncation circle polynomial is supported in `{0, ..., J}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2086-L2093
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2086-L2093

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

theorem HermitekLEAN.truncCirclePoly_support :
    ∀ {k J : ℕ} (r : ℝ) (G : ℂ → ℂ),
      truncCirclePoly k r J G =
        positiveTrigonometricPolynomial
          (frequencyBand 0 (J + 1))
          (finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1)) := by sorry
