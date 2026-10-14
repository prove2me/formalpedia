-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_simplex_downward_cutoff
-- name    : OAI.PiExponent.FormalInterpolation.weighted_simplex_downward_cutoff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T07:41:43.284287+00:00
-- url     : https://prove2.me/theorems/af2c1e7a-5627-4ea6-8327-549d1ff673b8
-- title:
--   Downward cutoff for strict weighted simplexes
-- statement:
--   An exponent bounded coordinatewise by an exponent in the total-height strict weighted simplex lies in the factor’s strict weighted simplex whenever its weighted degree is below that factor’s positive height.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_simplex_downward_cutoff
    {m : Nat} {n : Nat} (v : Fin (m + 1) → Real) (R : Fin n → Real)
    (hR : ∀ i, 0 < R i) (a : Fin (m + 1) → Nat)
    (ha : a ∈ OAI.PiExponent.strictWeightedSimplex v (∑ i, R i))
    (i : Fin n) (b : Fin (m + 1) → Nat) (hba : b ≤ a)
    (hb : ∑ j, v j * (b j : Real) < R i) :
    b ∈ OAI.PiExponent.strictWeightedSimplex v (R i) := by sorry
