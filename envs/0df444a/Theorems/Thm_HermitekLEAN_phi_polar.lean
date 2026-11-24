-- Prove2me | Theorems.Thm_HermitekLEAN_phi_polar
-- name    : HermitekLEAN.phi_polar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:40.209884+00:00
-- url     : https://prove2.me/theorems/79247a12-68a6-4b2a-ac39-33cf8b0d2816
-- title:
--   Hermitek LEAN: phi polar
-- statement:
--   Polar formula for `Phi k n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L324-L374
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L324-L374

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

theorem HermitekLEAN.phi_polar :
    ∀ {k n : ℕ} {r : ℝ},
      0 < r →
        ∀ t : Circle,
          Phi k n (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                ((qkn k n r : ℂ) * fourier (n : ℤ) t) := by sorry
