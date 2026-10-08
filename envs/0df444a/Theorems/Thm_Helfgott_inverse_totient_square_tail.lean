-- Prove2me | Theorems.Thm_Helfgott_inverse_totient_square_tail
-- name    : Helfgott.inverse_totient_square_tail
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T02:17:27.653573+00:00
-- url     : https://prove2.me/theorems/c2b192f9-e803-446b-9192-5ea6174d288e
-- title:
--   Explicit inverse-totient-square remainder bound of ten over the cutoff
-- statement:
--   For every positive integer $Q$, the convergent inverse-totient-square tail satisfies
--
--   $$\sum_{q\ge Q}\frac1{\varphi(q)^2}\le\frac{10}{Q}.$$
--
--   Here $\varphi$ is Euler's totient. The estimate is uniform in the cutoff and gives an explicit $1/Q$ remainder for absolutely convergent arithmetic series bounded by inverse totient squares. In particular, it controls the discarded denominators in the ternary Goldbach Ramanujan singular series. The formal sum writes $q=k+Q$, with $k$ ranging over the nonnegative integers.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §3 and §7.2, equation (7.9); R. C. Vaughan, The Hardy-Littlewood Method, Chapter 3. This coarse explicit remainder is independently derived by a nonnegative divisor expansion and a checked Euler-product upper bound. Reused qualitative totient and Ramanujan arithmetic inputs are attributed in the proof. Written by Codex.

import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.PSeries
open scoped BigOperators

theorem Helfgott.inverse_totient_square_tail (Q : ℕ) (hQ : 0 < Q) :
    (∑' k : ℕ,1/(Nat.totient (k+Q):ℝ)^2) ≤ 10/(Q:ℝ) := by sorry
