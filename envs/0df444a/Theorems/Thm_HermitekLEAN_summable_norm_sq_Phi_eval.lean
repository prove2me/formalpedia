-- Prove2me | Theorems.Thm_HermitekLEAN_summable_norm_sq_Phi_eval
-- name    : HermitekLEAN.summable_norm_sq_Phi_eval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:53.122354+00:00
-- url     : https://prove2.me/theorems/30eb1c23-f689-4343-9509-6269389b6d45
-- title:
--   Hermitek LEAN: summable norm sq Phi eval
-- statement:
--   The squared Hermite basis values are summable at every point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L4648-L4650
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L4648-L4650

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

theorem HermitekLEAN.summable_norm_sq_Phi_eval (k : ℕ) (z : ℂ) :
    Summable (fun n : ℕ => ‖Phi k n z‖ ^ 2) := by sorry
