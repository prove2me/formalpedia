-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_weighted_bound
-- name    : OAI.PiExponent.DeterminantContradiction.translation_scalar_weighted_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:11:10.31168+00:00
-- url     : https://prove2.me/theorems/8101c655-a06f-4cfe-be3e-c887a31fa5c9
-- title:
--   Weighted estimate for a translation scalar
-- statement:
--   For a scalar assembled from center factors and logarithmic tails, prove the exponential bound from local center-error, choice-order, and truncation-budget hypotheses. This is the reusable weighted core: the tail coefficient estimate and its truncation vanishing give the weighted tail budget, which combines with the center bound and the lower bound on the weights. The zero tail coefficient case is handled by nonnegativity of the exponential.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_scalar_weighted_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) (C : ℝ) (hC : 0 ≤ C)
    (hε : ∀ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          period)‖ ≤ Real.exp (C - nu * fixedWeights d i))
    (hk : (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ))
    (hT : ∀ i : Fin d.m,
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
    (hTw : ∀ i : Fin d.m,
      d.F0 * fixedWeights d i ≤
        (d.v0 : ℝ) *
          MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) :
    ‖choiceScalar d r t‖ ≤
      Real.exp (-nu * (indexWeight d t.1 - rowWeight d r) +
        H * (nu / d.F0 + Real.log 2 / (d.v0 : ℝ) +
          (Real.log 4 + C) / d.wstar)) := by sorry
