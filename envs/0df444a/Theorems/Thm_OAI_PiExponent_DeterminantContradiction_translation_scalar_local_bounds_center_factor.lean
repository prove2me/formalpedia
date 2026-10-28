-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_center_factor
-- name    : OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_center_factor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:15:12.197222+00:00
-- url     : https://prove2.me/theorems/1bbad94e-8e3f-42d1-961e-235e0e98a97f
-- title:
--   Translation center factor bound
-- statement:
--   Bound the logarithmic prefactor below by zero and prove the local exponential estimate for each rational center. The proof uses the approximation bound, the center-period identity, and the ceiling slack between `log q` and its integer ceiling.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_center_factor
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) :
    0 ≤ Real.log (2 * (d.K : ℝ)) + nu ∧
    (∀ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          period)‖ ≤
        Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i)) := by sorry
