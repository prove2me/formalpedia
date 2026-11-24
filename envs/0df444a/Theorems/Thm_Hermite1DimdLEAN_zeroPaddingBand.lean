-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_zeroPaddingBand
-- name    : Hermite1DimdLEAN.zeroPaddingBand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:01.008609+00:00
-- url     : https://prove2.me/theorems/1d8e1edf-c5cc-475b-ab17-1d2d6386b263
-- title:
--   Hermite1 Dimd LEAN: zero Padding Band
-- statement:
--   Zero-padding turns arbitrary finite support inside a band into a full band.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L365-L410
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/DegreeBookkeeping.lean#L365-L410

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

theorem Hermite1DimdLEAN.zeroPaddingBand
    (N L : ℕ) (E : Finset ℕ) (b : ℕ → ℂ)
    (hE : ∀ n ∈ E, N ≤ n ∧ n < N + L) :
    ∃ c : Fin L → ℂ,
      positiveFrequencyPolynomial E b =
        bandLimitedPolynomial N L c := by sorry
