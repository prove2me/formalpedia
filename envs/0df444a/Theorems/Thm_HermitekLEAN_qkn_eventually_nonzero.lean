-- Prove2me | Theorems.Thm_HermitekLEAN_qkn_eventually_nonzero
-- name    : HermitekLEAN.qkn_eventually_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:56.152813+00:00
-- url     : https://prove2.me/theorems/1df7f641-7a17-4e60-8da2-584be1042278
-- title:
--   Hermitek LEAN: qkn eventually nonzero
-- statement:
--   The radial coefficient `qkn k n` is eventually nonvanishing on large radii.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L611-L622
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L611-L622

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

theorem HermitekLEAN.qkn_eventually_nonzero :
    ∀ k n : ℕ,
      ∃ R0 : ℝ,
        1 ≤ R0 ∧
          ∀ r ≥ R0, qkn k n r ≠ 0 := by sorry
