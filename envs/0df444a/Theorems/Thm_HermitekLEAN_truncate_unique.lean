-- Prove2me | Theorems.Thm_HermitekLEAN_truncate_unique
-- name    : HermitekLEAN.truncate_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:39.181261+00:00
-- url     : https://prove2.me/theorems/be005aad-9f42-44f7-a7c4-432b5063bd7c
-- title:
--   Hermitek LEAN: truncate unique
-- statement:
--   The truncation is the unique degree-`≤ J` element with the prescribed first coefficients.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2307-L2328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L2307-L2328

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

theorem HermitekLEAN.truncate_unique :
    ∀ {k J : ℕ} {G H : ℂ → ℂ},
      H ∈ Hk k →
        (∀ n : ℕ,
          hermiteCoeff k H n = if _h : n < J + 1 then hermiteCoeff k G n else 0) →
            H = truncate k J G := by sorry
