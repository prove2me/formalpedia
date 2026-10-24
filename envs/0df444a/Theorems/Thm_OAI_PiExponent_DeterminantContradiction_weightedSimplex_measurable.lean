-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_measurable
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_measurable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:57:20.625271+00:00
-- url     : https://prove2.me/theorems/81f1275f-009c-4410-9ca2-58e9134d154f
-- title:
--   Measurability of the weighted simplex
-- statement:
--   The weighted simplex is measurable as a finite intersection of closed coordinate half-spaces and the closed sublevel set of a continuous weighted sum. No positivity or nonnegativity assumption on the parameters is needed for measurability.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_measurable {m : Nat} (w : Fin m → Real) (A : Real) :
    MeasurableSet
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A} := by sorry
