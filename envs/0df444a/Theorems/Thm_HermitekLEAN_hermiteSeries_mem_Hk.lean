-- Prove2me | Theorems.Thm_HermitekLEAN_hermiteSeries_mem_Hk
-- name    : HermitekLEAN.hermiteSeries_mem_Hk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:31:34.74435+00:00
-- url     : https://prove2.me/theorems/fca7e29e-7d7e-4a61-9ab3-6e7965067457
-- title:
--   Hermitek LEAN: hermite Series mem Hk
-- statement:
--   A square-summable Hermite series defines an element of `H_k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L4613-L4638
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L4613-L4638

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

theorem HermitekLEAN.hermiteSeries_mem_Hk :
    ∀ {k : ℕ} (h : ℕ → ℂ),
      (∀ n, ‖h n‖ ≤ 1) →
      Summable (fun n => ‖h n‖ ^ 2) →
      hermiteSeries k h ∈ Hk k := by sorry
