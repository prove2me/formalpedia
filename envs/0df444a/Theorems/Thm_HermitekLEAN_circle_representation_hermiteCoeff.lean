-- Prove2me | Theorems.Thm_HermitekLEAN_circle_representation_hermiteCoeff
-- name    : HermitekLEAN.circle_representation_hermiteCoeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:27.635791+00:00
-- url     : https://prove2.me/theorems/206faf49-2c9a-4790-bcf0-3ca73074f0f0
-- title:
--   Hermitek LEAN: circle representation hermite Coeff
-- statement:
--   Canonical circle representation in terms of `hermiteCoeff`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2983-L3012
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2983-L3012

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

theorem HermitekLEAN.circle_representation_hermiteCoeff :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ, 0 < r →
          ∀ t : Circle,
            G (circlePoint r t) =
              circleLeadingFactor k r *
                (fourier (-(k : ℤ)) t : ℂ) *
                  circleSeries k (hermiteCoeff k G) r t := by sorry
