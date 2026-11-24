-- Prove2me | Theorems.Thm_HermiteLEAN_annulus_distance_lower_bound
-- name    : HermiteLEAN.annulus_distance_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:49.45198+00:00
-- url     : https://prove2.me/theorems/3e55112b-7eb8-4617-887c-07909ffee745
-- title:
--   Hermite LEAN: annulus distance lower bound
-- statement:
--   A convenient interval-distance lower bound for annulus arguments.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/MissingMathlib.lean#L38-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/MissingMathlib.lean#L38-L53

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

theorem HermiteLEAN.annulus_distance_lower_bound (j : ℕ) (x : ℝ) :
    posPart (|((j : ℕ) : ℝ) - x| - 1)
      ≤ min |((j : ℕ) : ℝ) - x| |(((j + 1 : ℕ) : ℝ) - x)| := by sorry
