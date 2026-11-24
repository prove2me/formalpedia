-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_partitionOfGaussianNorm
-- name    : Hermite1DimdLEAN.partitionOfGaussianNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:57.042631+00:00
-- url     : https://prove2.me/theorems/9253bbfa-7605-4189-bc8a-87aa542a6c14
-- title:
--   Hermite1 Dimd LEAN: partition Of Gaussian Norm
-- statement:
--   Partition of the Gaussian norm by product annuli.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L419-L458
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L419-L458

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

theorem Hermite1DimdLEAN.partitionOfGaussianNorm
    {d : ℕ} (F : CSpace d → ℂ)
    (hF : Integrable (fun z : CSpace d => ‖F z‖ ^ 2) (gaussianMeasure d)) :
    gaussianL2NormSq F = ∑' j : MultiIndex d, annulusMass j F := by sorry
