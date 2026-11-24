-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_annulusRotationAveraging
-- name    : Hermite1DimdLEAN.annulusRotationAveraging
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:13:06.873829+00:00
-- url     : https://prove2.me/theorems/eb78cb82-fa4a-46c7-8382-e5ff0c217183
-- title:
--   Hermite1 Dimd LEAN: annulus Rotation Averaging
-- statement:
--   Rotation averaging on a product annulus for nonnegative measurable functions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L820-L903
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L820-L903

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

theorem Hermite1DimdLEAN.annulusRotationAveraging
    {d : ℕ} (j : MultiIndex d) (F : CSpace d → ENNReal) (hF : Measurable F) :
    by
      classical
      exact
        ∫⁻ z : CSpace d,
            if _h : z ∈ productAnnulus j then
              ∫⁻ t : Hermite1DimdLEAN.Circle,
                  F (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                    ∂ AddCircle.haarAddCircle
            else 0
          ∂ gaussianMeasure d
          =
        ∫⁻ z : CSpace d, if _h : z ∈ productAnnulus j then F z else 0 ∂ gaussianMeasure d := by sorry
