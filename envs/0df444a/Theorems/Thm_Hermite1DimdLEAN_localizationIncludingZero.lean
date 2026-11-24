-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_localizationIncludingZero
-- name    : Hermite1DimdLEAN.localizationIncludingZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:12:39.253457+00:00
-- url     : https://prove2.me/theorems/5e145ba1-8eed-49da-8721-00200598414c
-- title:
--   Hermite1 Dimd LEAN: localization Including Zero
-- statement:
--   Project-owned upgrade of localization that now includes the zero mode.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L639-L723
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L639-L723

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

theorem Hermite1DimdLEAN.localizationIncludingZero
    (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n j : ℕ,
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) ≤
          C *
            Real.exp
              (-c *
                max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by sorry
