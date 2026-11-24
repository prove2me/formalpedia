-- Prove2me | Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
-- name    : HermitekLEAN.hermiteCoeff_phi0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:31.743465+00:00
-- url     : https://prove2.me/theorems/ebcac07c-7bc1-4087-9201-566e44bdf586
-- title:
--   Hermitek LEAN: hermite Coeff phi0
-- statement:
--   The zeroth coefficient is the inner product against the lowest basis vector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1844-L1847
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1844-L1847

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

theorem HermitekLEAN.hermiteCoeff_phi0 :
    ∀ {k : ℕ} {G : ℂ → ℂ}, hermiteCoeff k G 0 = weightedInner G (phi0 k) := by sorry
