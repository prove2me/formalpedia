-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_annulusOrthogonality
-- name    : Hermite1DimdLEAN.annulusOrthogonality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:07.791778+00:00
-- url     : https://prove2.me/theorems/7a5a3cae-5df3-456f-b3a4-a8ced73cb6df
-- title:
--   Hermite1 Dimd LEAN: annulus Orthogonality
-- statement:
--   Annulus orthogonality of distinct basis vectors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L906-L990
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L906-L990

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

theorem Hermite1DimdLEAN.annulusOrthogonality
    {d : ℕ} (κ j α β : MultiIndex d) (hαβ : α ≠ β) :
    annulusInner j (PhiKappaAlpha κ α) (PhiKappaAlpha κ β) = 0 := by sorry
