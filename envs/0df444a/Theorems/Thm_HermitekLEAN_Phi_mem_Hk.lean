-- Prove2me | Theorems.Thm_HermitekLEAN_Phi_mem_Hk
-- name    : HermitekLEAN.Phi_mem_Hk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:29:57.466543+00:00
-- url     : https://prove2.me/theorems/ff57b621-5d53-4c1c-a367-2efbec5485d7
-- title:
--   Hermitek LEAN: Phi mem Hk
-- statement:
--   Every basis vector belongs to the true level space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1686-L1697
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1686-L1697

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

theorem HermitekLEAN.Phi_mem_Hk (k n : ℕ) : Phi k n ∈ Hk k := by sorry
