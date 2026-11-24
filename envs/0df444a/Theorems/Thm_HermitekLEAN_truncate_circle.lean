-- Prove2me | Theorems.Thm_HermitekLEAN_truncate_circle
-- name    : HermitekLEAN.truncate_circle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:43.87788+00:00
-- url     : https://prove2.me/theorems/d5887c43-0546-461c-b7c6-30c6b4bf5b06
-- title:
--   Hermitek LEAN: truncate circle
-- statement:
--   Truncations admit the corresponding finite circle representation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2072-L2083
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2072-L2083

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

theorem HermitekLEAN.truncate_circle :
    ∀ (k J : ℕ) (G : ℂ → ℂ) {r : ℝ},
      0 < r →
        ∀ t : Circle,
          truncate k J G (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                truncCirclePoly k r J G t := by sorry
