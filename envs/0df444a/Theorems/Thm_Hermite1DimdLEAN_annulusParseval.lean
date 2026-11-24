-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_annulusParseval
-- name    : Hermite1DimdLEAN.annulusParseval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:45.102562+00:00
-- url     : https://prove2.me/theorems/9196bbe5-6a31-438e-9ccd-be55449f6c65
-- title:
--   Hermite1 Dimd LEAN: annulus Parseval
-- statement:
--   Annulus Parseval for finite Hermite sums.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L993-L1029
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L993-L1029

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

theorem Hermite1DimdLEAN.annulusParseval
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (G : FiniteHermiteSum d) :
    annulusMass j (evalHermiteSum κ G) =
      Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α) := by sorry
