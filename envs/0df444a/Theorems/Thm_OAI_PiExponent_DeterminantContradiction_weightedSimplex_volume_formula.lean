-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_formula
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:32:23.88289+00:00
-- url     : https://prove2.me/theorems/5d09e174-1541-472d-994d-cb568e9de8fb
-- title:
--   Volume of a positive weighted simplex
-- statement:
--   For positive weights and cutoff B, the real volume of the closed weighted simplex is B^m divided by m! and by the product of the weights. The empty-dimensional case gives 1 on both sides.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_formula {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B}).toReal =
      B ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by sorry
