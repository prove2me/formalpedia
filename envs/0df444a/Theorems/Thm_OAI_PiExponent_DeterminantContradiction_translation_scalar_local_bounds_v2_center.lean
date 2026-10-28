-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_v2_center
-- name    : OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_center
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:23:39.998733+00:00
-- url     : https://prove2.me/theorems/d102e0ba-87d6-4737-b2b8-99f340eb4b02
-- title:
--   Translation center factor estimate
-- statement:
--   Prove the nonnegative logarithmic prefactor and the local exponential estimate for each rational center. Use the approximation bound, the rational-center minus period identity, and the slack between the logarithm of a denominator and its integer ceiling. This isolates the analytic center estimate from the row-choice and truncation arithmetic.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_center
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) :
    0 ≤ Real.log (2 * (d.K : ℝ)) + nu ∧
    (∀ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          period)‖ ≤
        Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i)) := by sorry
