-- Prove2me | Theorems.Thm_HermitekLEAN_qkn_eventual_lower_bound
-- name    : HermitekLEAN.qkn_eventual_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:24.837683+00:00
-- url     : https://prove2.me/theorems/9b399c20-1b4f-4677-8879-f6ec3c117059
-- title:
--   Hermitek LEAN: qkn eventual lower bound
-- statement:
--   Each `qkn k n` eventually dominates a positive multiple of `r^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L574-L608
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L574-L608

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

theorem HermitekLEAN.qkn_eventual_lower_bound :
    ∀ k n : ℕ,
      ∃ R c : ℝ,
        1 ≤ R ∧
          0 < c ∧
            ∀ r ≥ R, c * r ^ n ≤ ‖(qkn k n r : ℂ)‖ := by sorry
