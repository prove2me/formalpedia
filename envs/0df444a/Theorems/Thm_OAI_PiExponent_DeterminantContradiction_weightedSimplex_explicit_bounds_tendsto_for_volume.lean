-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_explicit_bounds_tendsto_for_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_explicit_bounds_tendsto_for_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:59:46.147001+00:00
-- url     : https://prove2.me/theorems/58a300be-5f56-4f8b-b51e-85c9909752fa
-- title:
--   Convergence of the explicit simplex bounds to volume
-- statement:
--   For fixed positive weights and positive A, both explicit bounds converge to the volume of the simplex at cutoff A. One proof route applies the positive weighted-simplex volume formula at A, then uses 1/H → 0 and continuity of the fixed-degree power function. This removes the limit calculation from the parent; the volume identity and scalar limit remain to be proved here.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_explicit_bounds_tendsto_for_volume {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    Tendsto (fun H : Real => (A - (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) ∧
    Tendsto (fun H : Real => (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) := by sorry
