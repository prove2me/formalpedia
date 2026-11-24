-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_zeroFrequencyAbsent
-- name    : Hermite1DimdLEAN.zeroFrequencyAbsent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:12.191622+00:00
-- url     : https://prove2.me/theorems/057fe256-a9b5-4b40-8f0a-e7d6b91e92c6
-- title:
--   Hermite1 Dimd LEAN: zero Frequency Absent
-- statement:
--   Orthogonality to `ν_κ` removes zero from every local degree window.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L413-L436
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L413-L436

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

theorem Hermite1DimdLEAN.zeroFrequencyAbsent
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (horth : hermiteInnerNu κ G = 0) :
    0 ∉ localDegreeSet j M G := by sorry
