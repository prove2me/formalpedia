-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_productBasisOrthonormal
-- name    : Hermite1DimdLEAN.productBasisOrthonormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:34.357168+00:00
-- url     : https://prove2.me/theorems/edb4097e-ecb0-463c-84a5-da0fcb150207
-- title:
--   Hermite1 Dimd LEAN: product Basis Orthonormal
-- statement:
--   Product basis orthonormality at fixed multi-index `κ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L229-L263
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ProductBasisAndAnnuli.lean#L229-L263

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

theorem Hermite1DimdLEAN.productBasisOrthonormal
    {d : ℕ} (κ α β : MultiIndex d) :
    gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β) =
      if α = β then (1 : ℂ) else 0 := by sorry
