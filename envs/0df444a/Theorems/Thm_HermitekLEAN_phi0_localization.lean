-- Prove2me | Theorems.Thm_HermitekLEAN_phi0_localization
-- name    : HermitekLEAN.phi0_localization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:53.188655+00:00
-- url     : https://prove2.me/theorems/a1f8eabc-a894-4d9e-9750-f9e2e858e9f9
-- title:
--   Hermitek LEAN: phi0 localization
-- statement:
--   Localization of the lowest vector `Phi k 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/BasisLocalization.lean#L1178-L1265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/BasisLocalization.lean#L1178-L1265

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
noncomputable section
open HermitekLEAN

theorem HermitekLEAN.phi0_localization :
    ∀ k : ℕ,
      ∃ C c : ℝ,
        0 < C ∧ 0 < c ∧
          ∀ j : ℕ,
            annulusIntegralSq (phi0 k) j ≤
              C * Real.exp (-c * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := by sorry
