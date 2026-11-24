-- Prove2me | Theorems.Thm_HermitekLEAN_local_circle_estimate
-- name    : HermitekLEAN.local_circle_estimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:14.404212+00:00
-- url     : https://prove2.me/theorems/685c45f9-7b71-48fa-a438-70300f685652
-- title:
--   Hermitek LEAN: local circle estimate
-- statement:
--   Imported local circle estimate for positive frequencies.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ImportedAnalyticInputs.lean#L32-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/ImportedAnalyticInputs.lean#L32-L39

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Theorems.Thm_FockSPR_local_circle_estimate
public import Theorems.Thm_HermiteLEAN_local_circle_estimate

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermitekLEAN

theorem HermitekLEAN.local_circle_estimate
    (E : Finset ℕ)
    (hpos : ∀ n ∈ E, 1 ≤ n)
    (c : ℕ → ℂ) :
    circleL2Sq (positiveTrigonometricPolynomial E c)
      ≤ 144 * E.card * circleRhoNormSq (positiveTrigonometricPolynomial E c) := by sorry
