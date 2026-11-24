-- Prove2me | Theorems.Thm_HermitekLEAN_finiteHermiteSum_circle
-- name    : HermitekLEAN.finiteHermiteSum_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:17.027205+00:00
-- url     : https://prove2.me/theorems/03b7fcdb-d83c-4a00-a12f-d4d07656bc7a
-- title:
--   Hermitek LEAN: finite Hermite Sum circle
-- statement:
--   Finite Hermite sums admit a finite circle representation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1960-L2006
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1960-L2006

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

theorem HermitekLEAN.finiteHermiteSum_circle :
    ∀ {k D : ℕ} (a : Fin D → ℂ) {r : ℝ},
      0 < r →
        ∀ t : Circle,
          finiteHermiteSum k a (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                finiteCirclePoly k r a t := by sorry
