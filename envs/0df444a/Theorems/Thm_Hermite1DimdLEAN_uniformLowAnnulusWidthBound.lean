-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_uniformLowAnnulusWidthBound
-- name    : Hermite1DimdLEAN.uniformLowAnnulusWidthBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:09.550419+00:00
-- url     : https://prove2.me/theorems/6dcff946-c9f2-4e7c-a836-074a777bb9e1
-- title:
--   Hermite1 Dimd LEAN: uniform Low Annulus Width Bound
-- statement:
--   Uniform low-annulus width bound at the frozen threshold `J(d,M)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L163-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L163-L174

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN

theorem Hermite1DimdLEAN.uniformLowAnnulusWidthBound
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : annulusRadius j < degreeThreshold d M) :
    degreeWidth j M ≤ d * (degreeThreshold d M + M) ^ 2 := by sorry
