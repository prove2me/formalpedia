-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_le_expanded_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_expanded_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:05:39.240134+00:00
-- url     : https://prove2.me/theorems/49cb215d-01da-436b-b470-092f2454123a
-- title:
--   Weighted simplex count bounded by expanded volume
-- statement:
--   Establish the geometric counting estimate by measuring the disjoint union of half-open boxes indexed by the finite weighted simplex and bounding that union by the nonnegative simplex of radius B + ∑ w. At m = 0 the single empty-coordinate box and the zero-dimensional simplex both have volume 1. The independent proof route is to formalize the coordinate box map, prove pairwise disjointness from positivity of the weights and distinct natural vectors, compute each box's product measure, prove containment from the defining weighted-sum inequality, and apply the nonnegative simplex volume formula. This removes the main lattice-count and volume argument from the parent; it is the remaining core obligation.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_expanded_volume {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    ((OAI.PiExponent.realWeightedSimplex w B).card : Real) ≤
      (B + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by sorry
