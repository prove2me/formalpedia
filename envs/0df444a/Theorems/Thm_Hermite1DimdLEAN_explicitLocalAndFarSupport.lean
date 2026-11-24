-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_explicitLocalAndFarSupport
-- name    : Hermite1DimdLEAN.explicitLocalAndFarSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:23.466336+00:00
-- url     : https://prove2.me/theorems/0336dd31-e811-4726-9421-834115bb8de8
-- title:
--   Hermite1 Dimd LEAN: explicit Local And Far Support
-- statement:
--   Explicit local and far support sets relative to an annulus and width.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L219-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L219-L249

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

theorem Hermite1DimdLEAN.explicitLocalAndFarSupport
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Disjoint (localCoeffSet j M G) (farCoeffSet j M G) ∧
      localCoeffSet j M G ∪ farCoeffSet j M G = G.support ∧
      (localPart j M G).support = localCoeffSet j M G ∧
      (remainderPart j M G).support = farCoeffSet j M G := by sorry
