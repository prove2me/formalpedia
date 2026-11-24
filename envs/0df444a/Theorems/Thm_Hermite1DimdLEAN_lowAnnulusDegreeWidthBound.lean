-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_lowAnnulusDegreeWidthBound
-- name    : Hermite1DimdLEAN.lowAnnulusDegreeWidthBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:27.005269+00:00
-- url     : https://prove2.me/theorems/9642a3e8-1ee0-4c4a-9750-9cf208b47deb
-- title:
--   Hermite1 Dimd LEAN: low Annulus Degree Width Bound
-- statement:
--   Low-annulus crude width bound in terms of the annulus radius.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L155-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L155-L160

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

theorem Hermite1DimdLEAN.lowAnnulusDegreeWidthBound
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (_hj : annulusRadius j < M + 1) :
    degreeWidth j M ≤ d * (annulusRadius j + M + 1) ^ 2 := by sorry
