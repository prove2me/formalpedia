-- Prove2me | Theorems.Thm_HermitekLEAN_qkn_real
-- name    : HermitekLEAN.qkn_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:29.284499+00:00
-- url     : https://prove2.me/theorems/2d6f7d6b-6796-4300-a7b6-e3bad137fbb3
-- title:
--   Hermitek LEAN: qkn real
-- statement:
--   The circle coefficients `qkn` remain fixed by complex conjugation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L403-L405
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L403-L405

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

theorem HermitekLEAN.qkn_real :
    ∀ {k n : ℕ} {r : ℝ}, star (qkn k n r : ℂ) = (qkn k n r : ℂ) := by sorry
