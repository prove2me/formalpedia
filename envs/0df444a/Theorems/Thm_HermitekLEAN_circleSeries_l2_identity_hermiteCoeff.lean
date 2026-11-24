-- Prove2me | Theorems.Thm_HermitekLEAN_circleSeries_l2_identity_hermiteCoeff
-- name    : HermitekLEAN.circleSeries_l2_identity_hermiteCoeff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:40.988438+00:00
-- url     : https://prove2.me/theorems/9301c29a-aad8-4c27-9872-ad24da6fced6
-- title:
--   Hermitek LEAN: circle Series l2 identity hermite Coeff
-- statement:
--   Circle Parseval identity for the canonical coefficient sequence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3366-L3374
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3366-L3374

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

theorem HermitekLEAN.circleSeries_l2_identity_hermiteCoeff :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ,
          0 < r →
            circleL2Sq (circleSeries k (hermiteCoeff k G) r) =
              ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 * |qkn k n r| ^ 2 := by sorry
