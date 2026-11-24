-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_oneVariableBasisOrthonormal
-- name    : Hermite1DimdLEAN.oneVariableBasisOrthonormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:11.597815+00:00
-- url     : https://prove2.me/theorems/8594cc7d-197f-429b-918e-2f70cc11eb5b
-- title:
--   Hermite1 Dimd LEAN: one Variable Basis Orthonormal
-- statement:
--   Imported one-variable basis orthonormality at fixed true-Hermite level.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L413-L423
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L413-L423

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

theorem Hermite1DimdLEAN.oneVariableBasisOrthonormal
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      if m = n then (1 : ℂ) else 0 := by sorry
