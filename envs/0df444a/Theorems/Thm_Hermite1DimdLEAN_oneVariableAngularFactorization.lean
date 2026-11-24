-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_oneVariableAngularFactorization
-- name    : Hermite1DimdLEAN.oneVariableAngularFactorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:48.08736+00:00
-- url     : https://prove2.me/theorems/e25a2a8f-11d4-4564-9c32-e8bb2b906878
-- title:
--   Hermite1 Dimd LEAN: one Variable Angular Factorization
-- statement:
--   The Hermite1 Dimd LEAN construction uses the one Variable Angular Factorization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L883-L976
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L883-L976

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

theorem Hermite1DimdLEAN.oneVariableAngularFactorization
    (k n : ℕ) :
    ∃ radial : Polynomial ℝ,
      ∀ r t : ℝ,
        oneDimPhi k n ((r : ℂ) * Complex.exp (Complex.I * t)) =
          Complex.exp (Complex.I * ((((n : ℤ) - (k : ℤ)) : ℂ) * t)) *
            radial.eval₂ (algebraMap ℝ ℂ) r := by sorry
