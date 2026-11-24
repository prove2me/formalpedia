-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_degreeIntervalOrder
-- name    : Hermite1DimdLEAN.degreeIntervalOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:21.634792+00:00
-- url     : https://prove2.me/theorems/0bf1218a-0113-4fb4-9d3c-8b822533190b
-- title:
--   Hermite1 Dimd LEAN: degree Interval Order
-- statement:
--   Crude bounds on the degree interval in terms of the annulus radius.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L143-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L143-L152

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

theorem Hermite1DimdLEAN.degreeIntervalOrder
    {d : ℕ} (j : MultiIndex d) (M : ℕ) :
    degreeIntervalLower j M ≤ degreeIntervalUpper j M := by sorry
