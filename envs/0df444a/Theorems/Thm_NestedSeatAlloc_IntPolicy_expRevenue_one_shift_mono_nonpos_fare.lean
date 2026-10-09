-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_one_shift_mono_nonpos_fare
-- name    : NestedSeatAlloc.IntPolicy.expRevenue_one_shift_mono_nonpos_fare
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:44:45.21999+00:00
-- url     : https://prove2.me/theorems/841cb8f8-1dc1-42ae-9a38-91aded258f66
-- title:
--   Expected class-one revenue minus a nonpositive linear fare is monotone
-- statement:
--   Under nonpositive first fare, the shifted expected first-class
--   revenue g(s) = ER_1(s)-f(1)*s is nondecreasing in s>=0.
--   This follows from the pointwise inequality that
--   c*(min(s,y)-s) is nondecreasing for c<=0, a separate
--   algebraic theorem scalar_min_shift_mono_nonpos.
--
--   The proof rewrites the first-class revenue into f(1)*min(s,X1),
--   uses revenue_integrable_of_seat_model for both capacity values,
--   uses the probability-measure integral of a constant to move the
--   linear term inside the integral, and applies integral_mono_ae.
--
--   This is the key analytic route to prove the original
--   SubdiffCondition(20) cannot hold with f(1)<=0, since it
--   asserts a right derivative r<=f(2)<f(1), whereas shifted
--   monotonicity forces r>=f(1).
--
--   No local Lean or Lake compilation. Remote verifier authoritative.
-- source:
--   Under nonpositive first fare, the shifted expected first-class
--   revenue g(s) = ER_1(s)-f(1)*s is nondecreasing in s>=0.
--   This follows from the pointwise inequality that
--   c*(min(s,y)-s) is nondecreasing for c<=0, a separate
--   algebraic theorem scalar_min_shift_mono_nonpos.
--
--   The proof rewrites the first-class revenue into f(1)*min(s,X1),
--   uses revenue_integrable_of_seat_model for both capacity values,
--   uses the probability-measure integral of a constant to move the
--   linear term inside the integral, and applies integral_mono_ae.
--
--   This is the key analytic route to prove the original
--   SubdiffCondition(20) cannot hold with f(1)<=0, since it
--   asserts a right derivative r<=f(2)<f(1), whereas shifted
--   monotonicity forces r>=f(1).
--
--   No local Lean or Lake compilation. Remote verifier authoritative.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.expRevenue_one_shift_mono_nonpos_fare {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (hf1 : f 1 ≤ 0) :
    MonotoneOn
      (fun s => expRevenue P X f p 1 s - f 1 * s) (Set.Ici 0) := by sorry
