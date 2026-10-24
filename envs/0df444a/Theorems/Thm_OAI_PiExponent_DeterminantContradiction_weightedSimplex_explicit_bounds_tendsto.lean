-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_explicit_bounds_tendsto
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_explicit_bounds_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:33:08.529112+00:00
-- url     : https://prove2.me/theorems/8df2e7ce-6fca-49d7-a8a4-b3c1f6cdb815
-- title:
--   Convergence of the explicit simplex bounds
-- statement:
--   For fixed positive weights and A, both explicit expressions with cutoffs A − (∑ᵢ wᵢ)/H and A + (∑ᵢ wᵢ)/H converge to the real volume of the simplex with cutoff A.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_explicit_bounds_tendsto {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    Tendsto (fun H : Real => (A - (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) ∧
    Tendsto (fun H : Real => (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) := by sorry
