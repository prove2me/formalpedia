-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_region_volume_toReal
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_region_volume_toReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:44:23.184574+00:00
-- url     : https://prove2.me/theorems/d3cd91ce-bdf6-4d4e-8416-10dc7b16e18a
-- title:
--   Real volume of a weighted simplex
-- statement:
--   For positive coordinate weights and cutoff, the real-valued volume of the nonnegative weighted simplex is the cutoff to the dimension divided by the dimension factorial and the product of the weights. This follows by coordinate scaling and the standard simplex volume formula.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_region_volume_toReal {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal =
      A ^ m / ((m.factorial : Real) * ∏ i : Fin m, w i) := by sorry
