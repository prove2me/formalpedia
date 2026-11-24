-- Prove2me | Theorems.Thm_HermiteLEAN_local_circle_estimate
-- name    : HermiteLEAN.local_circle_estimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:35.014198+00:00
-- url     : https://prove2.me/theorems/8e8eb64d-991b-40f7-8022-edba62887d86
-- title:
--   Hermite LEAN: local circle estimate
-- statement:
--   Imported theorem A: local circle estimate for positive frequencies.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/ImportedAnalyticInputs.lean#L53-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/ImportedAnalyticInputs.lean#L53-L67

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCircleEstimate
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Theorems.Thm_FockSPR_local_circle_estimate

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermiteLEAN

theorem HermiteLEAN.local_circle_estimate
    (E : Finset ℕ)
    (hpos : ∀ n ∈ E, 1 ≤ n)
    (c : ℕ → ℂ) :
    circleL2Sq (positiveTrigonometricPolynomial E c)
      ≤ 144 * E.card * circleRhoNormSq (positiveTrigonometricPolynomial E c) := by sorry
