-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:24:36.238253+00:00
-- url     : https://prove2.me/theorems/427e7a71-52ce-4dcc-b834-16fec1b65061
-- title:
--   Weighted simplex lattice-count asymptotic
-- statement:
--   For fixed strictly positive weights, the number of natural lattice points in the strict weighted simplex, normalized by H to the dimension, tends to the simplex volume. The statement includes dimension zero, where the empty product and 0! give limit one. A proof can use scaled grid boxes and show that boxes meeting the simplex boundary have lower-order total volume; the strict cutoff affects only those boundary boxes.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : ℝ => ((strictWeightedSimplex w H).card : ℝ) / H ^ n) atTop
      (nhds (1 / ((n.factorial : ℝ) * ∏ i, w i))) := by sorry
