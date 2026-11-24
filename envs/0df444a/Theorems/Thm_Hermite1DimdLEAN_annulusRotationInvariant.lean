-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_annulusRotationInvariant
-- name    : Hermite1DimdLEAN.annulusRotationInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:01.024957+00:00
-- url     : https://prove2.me/theorems/8ca0ced2-ae9d-4e20-9922-cbda76d6f8af
-- title:
--   Hermite1 Dimd LEAN: annulus Rotation Invariant
-- statement:
--   Rotation preserves a product annulus.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L608-L613
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L608-L613

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

theorem Hermite1DimdLEAN.annulusRotationInvariant
    {d : ℕ} (j : MultiIndex d) (t : ℝ) (z : CSpace d) :
    z ∈ productAnnulus j ↔
      (fun q => Complex.exp (Complex.I * t) * z q) ∈ productAnnulus j := by sorry
