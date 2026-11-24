-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_localDegreeInterval
-- name    : Hermite1DimdLEAN.localDegreeInterval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:13:57.602724+00:00
-- url     : https://prove2.me/theorems/c545cc0f-065b-4cae-ac07-0e946bee2d3b
-- title:
--   Hermite1 Dimd LEAN: local Degree Interval
-- statement:
--   Local degree support lies in an explicit interval.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L67-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L67-L140

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

theorem Hermite1DimdLEAN.localDegreeInterval
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    (∀ n ∈ localDegreeSet j M G, degreeIntervalLower j M ≤ n ∧ n ≤ degreeIntervalUpper j M) ∧
      (localDegreeSet j M G).card ≤ degreeWidth j M := by sorry
