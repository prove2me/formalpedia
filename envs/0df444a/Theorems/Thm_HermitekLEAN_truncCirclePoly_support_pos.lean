-- Prove2me | Theorems.Thm_HermitekLEAN_truncCirclePoly_support_pos
-- name    : HermitekLEAN.truncCirclePoly_support_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:30:31.999096+00:00
-- url     : https://prove2.me/theorems/5cfeaaeb-3249-451e-b63f-c7fdc95d0ae4
-- title:
--   Hermitek LEAN: trunc Circle Poly support pos
-- statement:
--   Orthogonality to `Phi k 0` removes the zero frequency from every
--   truncation circle polynomial.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2097-L2108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2097-L2108

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

theorem HermitekLEAN.truncCirclePoly_support_pos :
    ∀ {k J : ℕ} (r : ℝ) (G : ℂ → ℂ),
      weightedInner G (phi0 k) = 0 →
        truncCirclePoly k r J G =
          positiveTrigonometricPolynomial
            (frequencyBand 1 J)
            (finiteCircleCoeff k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1)) := by sorry
