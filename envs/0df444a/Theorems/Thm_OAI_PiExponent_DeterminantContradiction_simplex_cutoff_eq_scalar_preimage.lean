-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_eq_scalar_preimage
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_cutoff_eq_scalar_preimage
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:03:15.066895+00:00
-- url     : https://prove2.me/theorems/3fd04804-0d34-421b-b4cc-dd8dfc911de5
-- title:
--   Simplex cutoff as a scalar preimage
-- statement:
--   For a positive cutoff r, the simplex with coordinate sum at most r is exactly the preimage of the unit simplex under scalar multiplication by r⁻¹. Positivity ensures this dilation preserves coordinate nonnegativity and converts the sum bound by dividing through by r. This also handles n = 0, where both sum constraints are vacuous and the unique point is preserved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_cutoff_eq_scalar_preimage
    (n : Nat) (r : Real) (hr : 0 ≤ r) (hpos : 0 < r) :
    {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ r} =
      (fun y : Fin n → Real => r⁻¹ • y) ⁻¹'
        {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ 1} := by sorry
