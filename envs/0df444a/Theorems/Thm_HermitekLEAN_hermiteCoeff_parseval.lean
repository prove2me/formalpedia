-- Prove2me | Theorems.Thm_HermitekLEAN_hermiteCoeff_parseval
-- name    : HermitekLEAN.hermiteCoeff_parseval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:26.045829+00:00
-- url     : https://prove2.me/theorems/78036842-95b0-4d4d-9625-9b97346f9844
-- title:
--   Hermitek LEAN: hermite Coeff parseval
-- statement:
--   Parseval identity for the canonical Hermite coefficients.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2910-L2932
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2910-L2932

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

theorem HermitekLEAN.hermiteCoeff_parseval :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        weightedNormSq G = ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 := by sorry
