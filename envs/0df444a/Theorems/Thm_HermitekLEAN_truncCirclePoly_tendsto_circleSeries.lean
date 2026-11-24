-- Prove2me | Theorems.Thm_HermitekLEAN_truncCirclePoly_tendsto_circleSeries
-- name    : HermitekLEAN.truncCirclePoly_tendsto_circleSeries
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:31:19.348628+00:00
-- url     : https://prove2.me/theorems/bf2e7fe3-924e-4c8a-8d05-484465e550d1
-- title:
--   Hermitek LEAN: trunc Circle Poly tendsto circle Series
-- statement:
--   The finite circle polynomials of `G` converge in circle `L²` to the Hermite circle series.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3732-L3855
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3732-L3855

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

theorem HermitekLEAN.truncCirclePoly_tendsto_circleSeries :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ,
          0 < r →
            ∀ ε : ℝ,
              0 < ε →
                ∃ J0 : ℕ,
                  ∀ J ≥ J0,
                    circleL2Sq
                        (truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r) ≤
                      ε := by sorry
