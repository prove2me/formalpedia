-- Prove2me | Theorems.Thm_HermitekLEAN_integrable_truncate_normSq_exp
-- name    : HermitekLEAN.integrable_truncate_normSq_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:24.824175+00:00
-- url     : https://prove2.me/theorems/3568c3a5-6ea8-41f4-83cd-5e32ebe5eee3
-- title:
--   Hermitek LEAN: integrable truncate norm Sq exp
-- statement:
--   Integrability of truncation norm squared with Gaussian weight.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2359-L2361
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2359-L2361

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

theorem HermitekLEAN.integrable_truncate_normSq_exp (k J : ℕ) (G : ℂ → ℂ) :
    Integrable (fun z : ℂ => ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by sorry
