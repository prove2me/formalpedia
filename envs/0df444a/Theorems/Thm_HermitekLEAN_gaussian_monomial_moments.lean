-- Prove2me | Theorems.Thm_HermitekLEAN_gaussian_monomial_moments
-- name    : HermitekLEAN.gaussian_monomial_moments
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:29:43.818071+00:00
-- url     : https://prove2.me/theorems/14dcd9ed-a7d9-4f6f-89f1-a493a07962aa
-- title:
--   Hermitek LEAN: gaussian monomial moments
-- statement:
--   Gaussian monomial moments in the weighted plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L261-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean#L261-L277

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

theorem HermitekLEAN.gaussian_monomial_moments :
    ∀ (a b : ℕ),
      (1 / Real.pi) *
          ∫ z : ℂ, ((z ^ a) * (star z) ^ b).re * Real.exp (-‖z‖ ^ 2)
        = if a = b then (Nat.factorial a : ℝ) else 0 := by sorry
