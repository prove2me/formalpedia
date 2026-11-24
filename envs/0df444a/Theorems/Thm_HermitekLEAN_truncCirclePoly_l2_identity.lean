-- Prove2me | Theorems.Thm_HermitekLEAN_truncCirclePoly_l2_identity
-- name    : HermitekLEAN.truncCirclePoly_l2_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:30:40.418414+00:00
-- url     : https://prove2.me/theorems/e32ecb50-c1e3-4487-b939-ead1f598cf87
-- title:
--   Hermitek LEAN: trunc Circle Poly l2 identity
-- statement:
--   Circle Parseval identity for truncated Hermite sums.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2111-L2118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2111-L2118

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

theorem HermitekLEAN.truncCirclePoly_l2_identity :
    ∀ (k J : ℕ) (r : ℝ) (G : ℂ → ℂ),
      circleL2Sq (truncCirclePoly k r J G) =
        ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 * |qkn k n.1 r| ^ 2 := by sorry
