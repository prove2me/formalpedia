-- Prove2me | Theorems.Thm_HermitekLEAN_integrable_weightedDiag
-- name    : HermitekLEAN.integrable_weightedDiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:03.073922+00:00
-- url     : https://prove2.me/theorems/523fd2b7-3077-462d-b549-2902717a03eb
-- title:
--   Hermitek LEAN: integrable weighted Diag
-- statement:
--   The Hermitek LEAN construction uses the integrable weighted Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1274-L1297
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1274-L1297

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

theorem HermitekLEAN.integrable_weightedDiag (k n : ℕ) :
    Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by sorry
