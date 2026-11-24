-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_blockDecompositionNorm
-- name    : Hermite1DimdLEAN.blockDecompositionNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:30.457612+00:00
-- url     : https://prove2.me/theorems/6fff4c54-01aa-48f1-a579-69fa46960d71
-- title:
--   Hermite1 Dimd LEAN: block Decomposition Norm
-- statement:
--   Orthogonal block decomposition by square blocks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L108-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L108-L120

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

theorem Hermite1DimdLEAN.blockDecompositionNorm
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteNormSq κ G = ∑' ℓ : MultiIndex d, hermiteNormSq κ (blockPart ℓ G) := by sorry
