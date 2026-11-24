-- Prove2me | Theorems.Thm_HermiteLEAN_polynomial_times_gaussian_le_gaussian
-- name    : HermiteLEAN.polynomial_times_gaussian_le_gaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:26.069804+00:00
-- url     : https://prove2.me/theorems/e6cfc6ca-61f1-4bfe-a898-048417515ef3
-- title:
--   Hermite LEAN: polynomial times gaussian le gaussian
-- statement:
--   A reusable Gaussian absorption lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/MissingMathlib.lean#L57-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/MissingMathlib.lean#L57-L112

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset Filter
open scoped BigOperators ComplexConjugate Topology
noncomputable section
open HermiteLEAN

theorem HermiteLEAN.polynomial_times_gaussian_le_gaussian
    {a : ℝ}
    (ha : 0 < a)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 0 ≤ x →
        (1 + x ^ k) * Real.exp (-a * x ^ 2)
          ≤ C * Real.exp (-(a / 2) * x ^ 2) := by sorry
