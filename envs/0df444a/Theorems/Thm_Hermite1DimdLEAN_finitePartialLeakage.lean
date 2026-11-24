-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_finitePartialLeakage
-- name    : Hermite1DimdLEAN.finitePartialLeakage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:58.558455+00:00
-- url     : https://prove2.me/theorems/9ee446cc-5351-419b-aa3e-c4cfb6666695
-- title:
--   Hermite1 Dimd LEAN: finite Partial Leakage
-- statement:
--   Leakage coefficient tends to zero and controls all finite partial remainder sums.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L1405-L1424
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L1405-L1424

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

theorem Hermite1DimdLEAN.finitePartialLeakage
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      Filter.Tendsto
        (fun M : ℕ => localizationLeakageCoefficient C c B d M)
        Filter.atTop (nhds 0) ∧
      ∀ (s : Finset (MultiIndex d)) (M : ℕ) (G : FiniteHermiteSum d),
        ∑ j ∈ s, annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
          localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by sorry
