-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_productAnnulusEstimate
-- name    : Hermite1DimdLEAN.productAnnulusEstimate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:43:54.588798+00:00
-- url     : https://prove2.me/theorems/78b00fdb-c708-4a56-925e-a047c7ae621b
-- title:
--   Hermite1 Dimd LEAN: product Annulus Estimate
-- statement:
--   Annulus-local circle estimate for the local window.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductAnnulusCircle.lean#L769-L834
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductAnnulusCircle.lean#L769-L834

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductAnnulusCircle
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN

theorem Hermite1DimdLEAN.productAnnulusEstimate
    {d : ℕ} (hd : 1 ≤ d) (κ : MultiIndex d) (M : ℕ) (j : MultiIndex d)
    (G : FiniteHermiteSum d)
    (horth : hermiteInnerNu κ G = 0) :
    annulusMass j (evalHermiteSum κ (localPart j M G)) ≤
      productAnnulusConstantSq d M *
        defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G)) := by sorry
