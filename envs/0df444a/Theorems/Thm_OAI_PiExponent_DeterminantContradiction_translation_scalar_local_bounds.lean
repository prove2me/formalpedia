-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds
-- name    : OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:10:55.377734+00:00
-- url     : https://prove2.me/theorems/71f997cd-393b-42c3-a3ad-bebd741a8c45
-- title:
--   Local bounds for one translation scalar
-- statement:
--   From the approximation, row, and truncation hypotheses, prove the center-factor exponential estimate, the choice-order bound, and the positive truncation and weighted truncation bounds needed by the scalar estimate. The center estimate follows the pinned `actual_error_exp` argument; the order bound follows from the row-weight constraint; the truncation bounds follow from the ceiling definition. Equality in the budget bounds is permitted.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) :
    0 ≤ Real.log (2 * (d.K : ℝ)) + nu ∧
    (∀ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          period)‖ ≤
        Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i)) ∧
    (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) ∧
    (∀ i : Fin d.m,
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) ∧
    (∀ i : Fin d.m,
      d.F0 * fixedWeights d i ≤
        (d.v0 : ℝ) *
          MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) := by sorry
