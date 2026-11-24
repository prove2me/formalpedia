-- Prove2me | Theorems.Thm_HermitekLEAN_integrable_weightedCross
-- name    : HermitekLEAN.integrable_weightedCross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:34.824432+00:00
-- url     : https://prove2.me/theorems/7deb83e9-b097-469b-8039-598da1e2be79
-- title:
--   Hermitek LEAN: integrable weighted Cross
-- statement:
--   The Hermitek LEAN construction uses the integrable weighted Cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1299-L1344
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1299-L1344

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN

theorem HermitekLEAN.integrable_weightedCross (k m n : ℕ) :
    Integrable (fun z : ℂ =>
      Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by sorry
