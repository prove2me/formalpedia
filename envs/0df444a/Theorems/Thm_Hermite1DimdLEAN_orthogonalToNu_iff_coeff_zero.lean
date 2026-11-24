-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_orthogonalToNu_iff_coeff_zero
-- name    : Hermite1DimdLEAN.orthogonalToNu_iff_coeff_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:12:55.636097+00:00
-- url     : https://prove2.me/theorems/2ee4355c-43cf-4dce-a4bc-a66a917b7323
-- title:
--   Hermite1 Dimd LEAN: orthogonal To Nu iff coeff zero
-- statement:
--   Orthogonality to `ν_κ` is equivalent to vanishing zero coefficient.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L338-L340
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L338-L340

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

theorem Hermite1DimdLEAN.orthogonalToNu_iff_coeff_zero
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteInnerNu κ G = 0 ↔ G.coeff 0 = 0 := by sorry
