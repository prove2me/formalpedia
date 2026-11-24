-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_finiteLeakage
-- name    : Hermite1DimdLEAN.finiteLeakage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:16.538945+00:00
-- url     : https://prove2.me/theorems/0a8c1cbe-7374-46af-80a8-7124115b5f83
-- title:
--   Hermite1 Dimd LEAN: finite Leakage
-- statement:
--   Leakage coefficient tends to zero and controls the global remainder.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L1380-L1402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/BlockLocalization.lean#L1380-L1402

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

theorem Hermite1DimdLEAN.finiteLeakage
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      Filter.Tendsto
        (fun M : ℕ => localizationLeakageCoefficient C c B d M)
        Filter.atTop (nhds 0) ∧
      ∀ (M : ℕ) (G : FiniteHermiteSum d),
        ∑' j : MultiIndex d, annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
          localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by sorry
