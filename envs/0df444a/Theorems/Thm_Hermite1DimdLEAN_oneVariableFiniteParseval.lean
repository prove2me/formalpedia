-- Prove2me | Theorems.Thm_Hermite1DimdLEAN_oneVariableFiniteParseval
-- name    : Hermite1DimdLEAN.oneVariableFiniteParseval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:32:11.665402+00:00
-- url     : https://prove2.me/theorems/1e1adf44-f888-444d-a5fc-db0c60d722fc
-- title:
--   Hermite1 Dimd LEAN: one Variable Finite Parseval
-- statement:
--   Imported one-variable Parseval statement for finite coefficient families.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L426-L505
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/ImportedAnalyticInputs.lean#L426-L505

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN

theorem Hermite1DimdLEAN.oneVariableFiniteParseval
    (k : ℕ) (G : FiniteHermiteSum 1) :
    hermiteNormSq (d := 1) (fun _ => k) G =
      Finset.sum G.support fun n => ‖G.coeff n‖ ^ 2 := by sorry
