-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_5_1
-- name    : OnlineRealSampling.Exact.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:16.438303+00:00
-- url     : https://prove2.me/theorems/27929b8e-9d0e-4de6-9995-f126c7db59c1
-- title:
--   Proposition 5.1 — invariants of IntervalSample
-- statement:
--   Let $F$ have a valid oracle, $M\ge1$, $0\le Z<M$, and let $B_1,B_2,\dots$ be any bit sequence, with $Q=(Z+\sum_{j\ge1}B_j2^{-j})/M$. At the head of every iteration of IntervalSample$(F,(Z,M))$ the following hold:
--   $$r=\max\{0,\ t-\lfloor\lg M\rfloor\},\qquad(13)$$
--   $$\hat Q\le Q\le\hat Q+2^{-t+1},\qquad(14)$$
--   $$F(X^--1)\le Q\le F(X^+),\qquad(15)$$
--   with $F(-1)=0$ and $F(\infty)=1$.
--
--   These invariants show that the binary search keeps $Q$ inside the current interval; they underlie the correctness and the tail bounds of Section 5.
--
--   Differences from the source:
--   - encoding: in each iteration of IntervalSample → at every configuration of the run that is at the loop head (any number of steps after the start); reason: the loop head is where an iteration begins; the invariants are deterministic and hold for every bit sequence
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 5.1, PDF 10 / printed 9; proof PDF 11 / printed 10

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 5.1 (invariants of IntervalSample). At the head of every iteration of
`IntervalSample(F, (Z, M))`, with `Q = (Z + ∑_{j ≥ 1} B_j 2^{-j}) / M`:
(13) `r = max{0, t - ⌊lg M⌋}`; (14) `Q̂ ≤ Q ≤ Q̂ + 2^{-t+1}`;
(15) `F(X⁻ - 1) ≤ Q ≤ F(X⁺)`, with `F(-1) = 0` and `F(∞) = 1`. -/
theorem proposition_5_1 (w : ℕ) (O : CDFOracle) (hO : O.Valid) (M z : ℕ) (hM : 1 ≤ M)
    (hz : z < M) (ω : ℕ → Bool) (n : ℕ)
    (hhead : ((intervalSample w).iter O.toOracleAccess w ω (ISState.init z M) n).st.pc =
      ISPC.head) :
    (((intervalSample w).iter O.toOracleAccess w ω (ISState.init z M) n).st.r : ℤ) =
        max 0 ((((intervalSample w).iter O.toOracleAccess w ω (ISState.init z M) n).st.t : ℤ) -
          (Nat.log 2 M : ℤ)) ∧
      ((intervalSample w).iter O.toOracleAccess w ω (ISState.init z M) n).st.qhat ≤
        Qvar M z ω ∧
      Qvar M z ω ≤ ((intervalSample w).iter O.toOracleAccess w ω (ISState.init z M) n).st.qhat +
        2 / 2 ^ ((intervalSample w).iter O.toOracleAccess w ω (ISState.init z M) n).st.t ∧
      cdfPrev O.F ((intervalSample w).iter O.toOracleAccess w ω (ISState.init z M) n).st.lo ≤
        Qvar M z ω ∧
      Qvar M z ω ≤
        (match ((intervalSample w).iter O.toOracleAccess w ω (ISState.init z M) n).st.hi with
          | none => 1
          | some h => O.F h) := by sorry

end OnlineRealSampling.Exact
