-- Prove2me | Theorems.Thm_HermitekLEAN_qkn_ratio_control
-- name    : HermitekLEAN.qkn_ratio_control
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:26.55942+00:00
-- url     : https://prove2.me/theorems/5c073128-6159-4006-8e1a-cc2d8f7f3f24
-- title:
--   Hermitek LEAN: qkn ratio control
-- statement:
--   Lower modes are eventually suppressed by at least one power of `r`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L625-L685
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L625-L685

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

theorem HermitekLEAN.qkn_ratio_control :
    ∀ {k n d : ℕ},
      n < d →
        ∃ C R0 : ℝ,
          0 < C ∧
            1 ≤ R0 ∧
              ∀ r : ℝ,
                R0 ≤ r →
                  ‖((qkn k n r : ℂ) / (qkn k d r : ℂ))‖ ≤ C / r := by sorry
