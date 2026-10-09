-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_first_fare_positive_of_subdiff_condition
-- name    : NestedSeatAlloc.IntPolicy.first_fare_positive_of_subdiff_condition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:50:24.955102+00:00
-- url     : https://prove2.me/theorems/a3b91458-e4da-452b-bcfa-090e07dc2bb5
-- title:
--   Full protection-policy subdifferential condition forces the first fare to be positive
-- statement:
--   Positive first fare is a consequence of the full SubdiffCondition.
--
--   If f(1)<=0, the already published helper
--   expRevenue_one_shift_mono_nonpos_fare shows that
--   s -> ER_1(s)-f(1)*s is nondecreasing for nonnegative s.
--   Condition (20) at k=1 supplies a right derivative r of ER_1
--   at p(1) satisfying r<=f(2). The shifted function has derivative
--   r-f(1) on the right. Since it is monotone, that derivative
--   cannot be negative. Therefore f(1)<=r<=f(2), contradicting
--   the strict fare decrease f(2)<f(1) in IsSeatModel.
--
--   The only topological detail is that the real right half-line
--   at p(1) has an accumulation point; accPt_iff_frequently and
--   frequently_gt_nhds provide it. This is mathematically necessary
--   to remove the extra positivity premise from the now Proved
--   full Theorem 1 reduction. The exact Mathlib signatures are being
--   confirmed with a remote signature probe. No local Lean/Lake.
-- source:
--   Positive first fare is a consequence of the full SubdiffCondition.
--
--   If f(1)<=0, the already published helper
--   expRevenue_one_shift_mono_nonpos_fare shows that
--   s -> ER_1(s)-f(1)*s is nondecreasing for nonnegative s.
--   Condition (20) at k=1 supplies a right derivative r of ER_1
--   at p(1) satisfying r<=f(2). The shifted function has derivative
--   r-f(1) on the right. Since it is monotone, that derivative
--   cannot be negative. Therefore f(1)<=r<=f(2), contradicting
--   the strict fare decrease f(2)<f(1) in IsSeatModel.
--
--   The only topological detail is that the real right half-line
--   at p(1) has an accumulation point; accPt_iff_frequently and
--   frequently_gt_nhds provide it. This is mathematically necessary
--   to remove the extra positivity premise from the now Proved
--   full Theorem 1 reduction. The exact Mathlib signatures are being
--   confirmed with a remote signature probe. No local Lean/Lake.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.first_fare_positive_of_subdiff_condition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p) :
    0 < f 1 := by sorry
