-- Prove2me | Theorems.Thm_HermitekLEAN_finiteCirclePoly_l2_identity
-- name    : HermitekLEAN.finiteCirclePoly_l2_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:15.460387+00:00
-- url     : https://prove2.me/theorems/c3bb40aa-b708-4ae7-bfb0-2fd8f3a5a1d5
-- title:
--   Hermitek LEAN: finite Circle Poly l2 identity
-- statement:
--   Circle Parseval identity for finite Hermite sums.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2045-L2069
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2045-L2069

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

theorem HermitekLEAN.finiteCirclePoly_l2_identity :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ),
      circleL2Sq (finiteCirclePoly k r a) =
        ∑ n : Fin D, ‖a n‖ ^ 2 * |qkn k n.1 r| ^ 2 := by sorry
