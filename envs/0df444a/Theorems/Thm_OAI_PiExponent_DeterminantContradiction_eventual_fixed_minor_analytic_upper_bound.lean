-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_analytic_upper_bound
-- name    : OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_analytic_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T19:19:09.120442+00:00
-- url     : https://prove2.me/theorems/86967b12-c5cd-4b3c-926f-627a85736630
-- title:
--   Asymptotic analytic upper bound for nonzero fixed minors
-- statement:
--   For every positive slack, all sufficiently large positive heights with nonempty row sets satisfy the analytic aggregate determinant upper bound, uniformly over nonzero selected minors.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_analytic_upper_bound
    (nu : Real) (d : FixedData nu) (delta : Real) (hdelta : 0 < delta) :
    ∀ᶠ H : Real in atTop, 0 < H → 0 < actualRowCount d H →
      ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
          Real.log ‖(actualMinor d H selection).det‖ /
              ((actualRowCount d H : Real) * H) ≤
            d.analyticError + delta +
              max (-collisionRate d H)
                (-nu * ((d.base.A : Real) * (1 - d.base.eta) -
                  actualMean d H)) := by sorry
