-- Prove2me | Theorems.Thm_HermitekLEAN_point_eval_bounded
-- name    : HermitekLEAN.point_eval_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:37.461402+00:00
-- url     : https://prove2.me/theorems/dfd104c8-8838-4ca3-b3e3-4f591b9a5aa3
-- title:
--   Hermitek LEAN: point eval bounded
-- statement:
--   Point evaluations are bounded on `H_k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3103-L3153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L3103-L3153

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

theorem HermitekLEAN.point_eval_bounded :
    ∀ {k : ℕ} (z : ℂ),
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ {G : ℂ → ℂ}, G ∈ Hk k → ‖G z‖ ≤ C * weightedNorm G := by sorry
