-- Prove2me | Theorems.Thm_HermitekLEAN_high_frequency_circle_estimate
-- name    : HermitekLEAN.high_frequency_circle_estimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:51.139446+00:00
-- url     : https://prove2.me/theorems/3e98ed26-4af3-4a78-ac67-c0c0b8c5c837
-- title:
--   Hermitek LEAN: high frequency circle estimate
-- statement:
--   Imported high-frequency circle estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ImportedAnalyticInputs.lean#L42-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ImportedAnalyticInputs.lean#L42-L51

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Theorems.Thm_HermiteLEAN_high_frequency_circle_estimate

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermitekLEAN

theorem HermitekLEAN.high_frequency_circle_estimate
    (N L : ℕ)
    (hN : 1 ≤ N)
    (hL : 1 ≤ L)
    (c : ℕ → ℂ)
    (hband : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2) :
    circleL2Sq (positiveTrigonometricPolynomial (frequencyBand N L) c)
      ≤ 32 * circleRhoNormSq (positiveTrigonometricPolynomial (frequencyBand N L) c) := by sorry
