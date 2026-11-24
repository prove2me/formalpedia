-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_productBasisLocalization
-- name    : Hermite1DimdLEAN.productBasisLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:53.157827+00:00
-- url     : https://prove2.me/theorems/67ed3854-5a67-4a51-943c-fac5bfb44eaf
-- title:
--   Hermite1 Dimd LEAN: product Basis Localization
-- statement:
--   Single-basis localization on a product annulus.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L631-L778
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L631-L778

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN

theorem Hermite1DimdLEAN.productBasisLocalization
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      ∀ α j ℓ : MultiIndex d, α ∈ squareBlock ℓ →
        annulusMass j (PhiKappaAlpha κ α) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by sorry
