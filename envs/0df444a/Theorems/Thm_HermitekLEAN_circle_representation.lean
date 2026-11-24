-- Prove2me | Theorems.Thm_HermitekLEAN_circle_representation
-- name    : HermitekLEAN.circle_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:30:51.080309+00:00
-- url     : https://prove2.me/theorems/fc832261-6721-4d4b-81a2-19d863ce5377
-- title:
--   Hermitek LEAN: circle representation
-- statement:
--   Compatibility statement: polar/circle representation of an element of `H_k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2946-L2980
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2946-L2980

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

theorem HermitekLEAN.circle_representation :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∃ g : ℕ → ℂ,
          G = hermiteSeries k g ∧
            ∀ r : ℝ, 0 < r →
              ∀ t : Circle,
                G (circlePoint r t) =
                  circleLeadingFactor k r *
                    (fourier (-(k : ℤ)) t : ℂ) *
                      circleSeries k g r t := by sorry
