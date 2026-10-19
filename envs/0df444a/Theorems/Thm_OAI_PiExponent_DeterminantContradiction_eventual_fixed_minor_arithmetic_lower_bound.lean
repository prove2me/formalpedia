-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_arithmetic_lower_bound
-- name    : OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T19:18:53.868341+00:00
-- url     : https://prove2.me/theorems/49438e40-7dbf-45ac-8c75-3a4c53f8d7ad
-- title:
--   Asymptotic arithmetic lower bound for nonzero fixed minors
-- statement:
--   For every positive slack, all sufficiently large positive heights with nonempty row sets satisfy the normalized arithmetic determinant lower bound, uniformly over nonzero selected minors.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound
    (nu : Real) (d : FixedData nu) (delta : Real) (hdelta : 0 < delta) :
    ∀ᶠ H : Real in atTop, 0 < H → 0 < actualRowCount d H →
      ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
          actualMean d H - 1 - d.arithmeticError - delta ≤
            Real.log ‖(actualMinor d H selection).det‖ /
              ((actualRowCount d H : Real) * H) := by sorry
