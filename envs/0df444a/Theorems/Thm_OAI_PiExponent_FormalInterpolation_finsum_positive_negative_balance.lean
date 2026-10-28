-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_positive_negative_balance
-- name    : OAI.PiExponent.FormalInterpolation.finsum_positive_negative_balance
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:22:20.381444+00:00
-- url     : https://prove2.me/theorems/9730d781-962d-408d-9547-285e7375bb33
-- title:
--   Positive and negative parts of a finite-support zero sum
-- statement:
--   For an integer-valued function with finite support, if the sum of its values in `Real` is zero, then the sums of its positive and negative parts agree. Restrict both sums to the finite support, split each integer into its nonnegative and negative parts, and use the zero-sum hypothesis. This removes only the finite algebraic bookkeeping from the parent; the valuation and divisor argument remains in the first child.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finsum_positive_negative_balance
    {ι : Type} (v : ι → Int)
    (hfinite : (Function.support v).Finite)
    (hsum : (∑ᶠ i : ι, (v i : Real)) = 0) :
    (∑ᶠ i : ι, max 0 (v i : Real)) =
      (∑ᶠ i : ι, max 0 (-(v i : Real))) := by
  sorry
