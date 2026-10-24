-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_ratFunc_euler_constant_obstruction
-- name    : OAI.PiExponent.FormalInterpolation.ratFunc_euler_constant_obstruction
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:23:00.691224+00:00
-- url     : https://prove2.me/theorems/8a753196-8f1c-4bc9-bbfc-e62568e20646
-- title:
--   The rational Euler derivation has no nonzero constant in its image
-- statement:
--   Construct d=X·d/dX by the quotient rule d(p/q)=X(p′q−pq′)/q². For the obstruction, handle r=0 separately and write any nonzero r=X^m P/Q, where m is an integer and P(0)Q(0)≠0. Then d(r)=X^m[mPQ+X(P′Q−PQ′)]/Q². If m≠0, characteristic zero makes the bracket nonzero at zero, so d(r) has order m and cannot be a nonzero constant. If m=0, d(r) is zero or has positive order, again excluding a nonzero constant. Equivalently, its constant Laurent coefficient is zero. RatFunc.induction_on and Derivation.leibniz_div provide the quotient machinery. This child isolates the one-variable obstruction without finite extensions or logarithmic primitives. The exclusion c≠0 is essential: zero and constant rational functions have derivative zero.

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic

theorem OAI.PiExponent.FormalInterpolation.ratFunc_euler_constant_obstruction
    (K : Type) [Field K] [CharZero K] :
    ∃ d : Derivation K (RatFunc K) (RatFunc K),
      d RatFunc.X = RatFunc.X ∧
      ∀ (r : RatFunc K) (c : K), c ≠ 0 →
        d r ≠ algebraMap K (RatFunc K) c := by sorry
