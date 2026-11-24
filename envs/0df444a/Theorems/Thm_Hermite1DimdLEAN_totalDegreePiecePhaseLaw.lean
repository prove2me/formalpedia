-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_totalDegreePiecePhaseLaw
-- name    : Hermite1DimdLEAN.totalDegreePiecePhaseLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:32:39.054395+00:00
-- url     : https://prove2.me/theorems/0a1bc20a-d93a-40db-8886-3ae71eef7094
-- title:
--   Hermite1 Dimd LEAN: total Degree Piece Phase Law
-- statement:
--   The same phase law for a fixed total-degree piece.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L403-L416
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L403-L416

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

theorem Hermite1DimdLEAN.totalDegreePiecePhaseLaw
    {d : ℕ} (κ : MultiIndex d) (n : ℕ) (G : FiniteHermiteSum d) (t : ℝ) (z : CSpace d) :
    evalHermiteSum κ (totalDegreePiece n G) (fun q => Complex.exp (Complex.I * t) * z q) =
      Complex.exp (Complex.I * (((n : ℤ) - (totalDegree κ : ℤ) : ℂ) * t)) *
        evalHermiteSum κ (totalDegreePiece n G) z := by sorry
