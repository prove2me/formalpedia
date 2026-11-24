-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_highAnnulusDegreeBounds
-- name    : Hermite1DimdLEAN.highAnnulusDegreeBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:55.411806+00:00
-- url     : https://prove2.me/theorems/94b54baf-f36d-4432-87d6-63b93888c0a6
-- title:
--   Hermite1 Dimd LEAN: high Annulus Degree Bounds
-- statement:
--   High-annulus crude degree lower/width upper bounds in terms of the annulus radius.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L266-L308
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L266-L308

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

theorem Hermite1DimdLEAN.highAnnulusDegreeBounds
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : M + 1 ≤ annulusRadius j) :
    (annulusRadius j - M) ^ 2 ≤ degreeIntervalLower j M ∧
      degreeWidth j M ≤ d * (2 * M + 1) * (2 * annulusRadius j + 1) := by sorry
