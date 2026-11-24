-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_annulusIntegrablePolynomial
-- name    : Hermite1DimdLEAN.annulusIntegrablePolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:20.542796+00:00
-- url     : https://prove2.me/theorems/0c4f216a-12f9-468d-9a17-f19eb3ee8559
-- title:
--   Hermite1 Dimd LEAN: annulus Integrable Polynomial
-- statement:
--   Finite-Hermite annulus integrability wrapper on a fixed annulus.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L461-L470
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L461-L470

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

theorem Hermite1DimdLEAN.annulusIntegrablePolynomial
    {d : ℕ} (j κ : MultiIndex d) (G H : FiniteHermiteSum d) :
    Integrable
      (indicatorMul (productAnnulus j)
        (fun z => evalHermiteSum κ G z * conj (evalHermiteSum κ H z)))
      (gaussianMeasure d) := by sorry
