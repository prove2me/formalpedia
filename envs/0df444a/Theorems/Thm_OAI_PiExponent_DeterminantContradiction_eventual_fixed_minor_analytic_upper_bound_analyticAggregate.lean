-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_analytic_upper_bound_analyticAggregate
-- name    : OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_analytic_upper_bound_analyticAggregate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T06:05:19.609495+00:00
-- url     : https://prove2.me/theorems/30983b30-634d-4281-83d0-c9ee99d36872
-- title:
--   Vanishing-error analytic bound for fixed minors
-- statement:
--   For fixed admissible data, a height-dependent error tending to zero bounds the normalized logarithm of every nonzero selected minor, uniformly for all sufficiently large heights. No additional hypothesis on nu is assumed, matching the exact target.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_analytic_upper_bound_analyticAggregate
    (nu : Real) (d : FixedData nu) :
    ∃ error : Real → Real, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : Real in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
          Real.log ‖(actualMinor d H selection).det‖ /
              ((actualRowCount d H : Real) * H) ≤
            d.analyticError + error H +
              max (-collisionRate d H)
                (-nu * ((d.base.A : Real) * (1 - d.base.eta) -
                  actualMean d H)) := by sorry
