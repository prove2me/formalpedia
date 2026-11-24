-- Prove2me | Theorems.Thm_HermiteLEAN_high_frequency_circle_estimate
-- name    : HermiteLEAN.high_frequency_circle_estimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:33.523782+00:00
-- url     : https://prove2.me/theorems/5e3a88c3-9682-4b99-9ad0-beebfea02717
-- title:
--   Hermite LEAN: high frequency circle estimate
-- statement:
--   Imported theorem B: high-frequency circle estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/ImportedAnalyticInputs.lean#L70-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/ImportedAnalyticInputs.lean#L70-L88

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCircleEstimate
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermiteLEAN

theorem HermiteLEAN.high_frequency_circle_estimate
    (N L : ℕ)
    (hN : 1 ≤ N)
    (hL : 1 ≤ L)
    (c : ℕ → ℂ)
    (hband : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2) :
    circleL2Sq (positiveTrigonometricPolynomial (frequencyBand N L) c)
      ≤ 32 * circleRhoNormSq (positiveTrigonometricPolynomial (frequencyBand N L) c) := by sorry
