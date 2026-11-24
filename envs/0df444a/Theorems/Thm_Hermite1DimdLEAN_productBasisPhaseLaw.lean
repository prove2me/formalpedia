-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_productBasisPhaseLaw
-- name    : Hermite1DimdLEAN.productBasisPhaseLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:34.843262+00:00
-- url     : https://prove2.me/theorems/9cd880bf-1821-43f7-88cf-2f39e99b55e0
-- title:
--   Hermite1 Dimd LEAN: product Basis Phase Law
-- statement:
--   Global phase law on the product basis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L374-L400
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L374-L400

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN

theorem Hermite1DimdLEAN.productBasisPhaseLaw
    {d : ℕ} (κ α : MultiIndex d) (t : ℝ) (z : CSpace d) :
    PhiKappaAlpha κ α (fun q => Complex.exp (Complex.I * t) * z q) =
      Complex.exp (Complex.I * (((totalDegree α : ℤ) - (totalDegree κ : ℤ) : ℂ) * t)) *
        PhiKappaAlpha κ α z := by sorry
