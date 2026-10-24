-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_explicit_scalar_bounds_tendsto_for_volume
-- name    : OAI.PiExponent.DeterminantContradiction.explicit_scalar_bounds_tendsto_for_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:38:43.85076+00:00
-- url     : https://prove2.me/theorems/b5914d56-3c50-4ba3-8552-a9240f9baa9f
-- title:
--   Scalar limits for the explicit simplex bounds
-- statement:
--   For fixed m, weights, and A, both expressions with A ± (∑ w i)/H converge as H tends to positive infinity to the expression with A. This removes the scalar limit calculation from the parent. An independent proof uses 1/H → 0 atTop and continuity of the fixed-degree power; the denominator product is nonzero by positivity of the weights. When m = 0, both sequences are constant 1.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.explicit_scalar_bounds_tendsto_for_volume {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : Real => (A - (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds (A ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i)) ∧
    Tendsto (fun H : Real => (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds (A ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i)) := by sorry
