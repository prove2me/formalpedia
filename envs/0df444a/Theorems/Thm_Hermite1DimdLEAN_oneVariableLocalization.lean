-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_oneVariableLocalization
-- name    : Hermite1DimdLEAN.oneVariableLocalization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:12:14.823429+00:00
-- url     : https://prove2.me/theorems/16106bf5-eb5d-4b5a-836b-09e7c6445bfc
-- title:
--   Hermite1 Dimd LEAN: one Variable Localization
-- statement:
--   Imported one-variable localization estimate for `n ≥ 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L508-L527
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L508-L527

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN

theorem Hermite1DimdLEAN.oneVariableLocalization
    (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n j : ℕ, 1 ≤ n →
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) ≤
          C *
            Real.exp
              (-c *
                max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by sorry
