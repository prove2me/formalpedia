-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_polynomialGaussianSeriesSummable
-- name    : Hermite1DimdLEAN.polynomialGaussianSeriesSummable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:42:11.281222+00:00
-- url     : https://prove2.me/theorems/0e5df17b-9d70-4e45-b659-b7f7160902ea
-- title:
--   Hermite1 Dimd LEAN: polynomial Gaussian Series Summable
-- statement:
--   Gaussian tails with polynomial weights are summable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L867-L875
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L867-L875

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN

theorem Hermite1DimdLEAN.polynomialGaussianSeriesSummable
    (m : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun r : ℕ => (r : ℝ) ^ m * Real.exp (-c * r ^ 2)) := by sorry
