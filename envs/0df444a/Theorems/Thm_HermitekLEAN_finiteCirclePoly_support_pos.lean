-- Prove2me | Theorems.Thm_HermitekLEAN_finiteCirclePoly_support_pos
-- name    : HermitekLEAN.finiteCirclePoly_support_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:31.689861+00:00
-- url     : https://prove2.me/theorems/a6b7bcae-f439-41b2-8473-500e21312daf
-- title:
--   Hermitek LEAN: finite Circle Poly support pos
-- statement:
--   If the zeroth coefficient vanishes, the finite circle polynomial has
--   positive-frequency support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2026-L2042
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2026-L2042

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

theorem HermitekLEAN.finiteCirclePoly_support_pos :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin (D + 1) → ℂ),
      a 0 = 0 →
        finiteCirclePoly k r a =
          positiveTrigonometricPolynomial (frequencyBand 1 D) (finiteCircleCoeff k r a) := by sorry
