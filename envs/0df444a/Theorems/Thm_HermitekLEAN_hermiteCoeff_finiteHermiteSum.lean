-- Prove2me | Theorems.Thm_HermitekLEAN_hermiteCoeff_finiteHermiteSum
-- name    : HermitekLEAN.hermiteCoeff_finiteHermiteSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:12.370843+00:00
-- url     : https://prove2.me/theorems/f322b239-8971-4b50-8421-c643511830cc
-- title:
--   Hermitek LEAN: hermite Coeff finite Hermite Sum
-- statement:
--   The canonical coefficient extractor recovers the coefficients of a finite Hermite sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1808-L1841
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L1808-L1841

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

theorem HermitekLEAN.hermiteCoeff_finiteHermiteSum :
    ∀ {k D : ℕ} (a : Fin D → ℂ) (n : ℕ),
      hermiteCoeff k (finiteHermiteSum k a) n = if h : n < D then a ⟨n, h⟩ else 0 := by sorry
