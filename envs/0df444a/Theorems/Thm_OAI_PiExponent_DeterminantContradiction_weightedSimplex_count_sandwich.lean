-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_count_sandwich
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_count_sandwich
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:34:36.361053+00:00
-- url     : https://prove2.me/theorems/218c203f-1e45-4520-8540-d63a29e063e1
-- title:
--   Weighted simplex lattice count is bounded by shifted simplex volumes
-- statement:
--   For fixed strictly positive weights, eventually the lattice count in the strict weighted simplex lies between the volumes of the simplices with heights shifted down and up by the sum of the weights. This also covers dimension zero, where both volume expressions equal one.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_count_sandwich
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∀ᶠ H : ℝ in atTop,
      ((H - ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i)) ≤
          ((strictWeightedSimplex w H).card : ℝ) ∧
        ((strictWeightedSimplex w H).card : ℝ) ≤
          ((H + ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i)) := by sorry
