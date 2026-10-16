-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_coordinates_mem_realWeightedSimplex
-- name    : OAI.PiExponent.FormalInterpolation.weighted_coordinates_mem_realWeightedSimplex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:54:25.628728+00:00
-- url     : https://prove2.me/theorems/2dde19d7-67d9-4fda-924f-ba8d3f4ac963
-- title:
--   A positive weighted bound places integer coordinates in the weighted simplex
-- statement:
--   For positive coordinate weights, any natural-valued coordinate function whose weighted sum is at most H belongs to the explicitly bounded weighted simplex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_coordinates_mem_realWeightedSimplex
    {d : Nat} (v : Fin d → Real) (H : Real)
    (hv : ∀ i, 0 < v i) (a : Fin d → Nat)
    (ha : ∑ i, v i * (a i : Real) ≤ H) :
    a ∈ OAI.PiExponent.realWeightedSimplex v H := by sorry
