-- Prove2me | Theorems.Thm_Helfgott_minor_arc_logarithmic_ratio_bound
-- name    : Helfgott.minor_arc_logarithmic_ratio_bound
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T00:54:23.981261+00:00
-- url     : https://prove2.me/theorems/0f522c13-110b-4e47-9c19-989ecdcf5cba
-- title:
--   Uniform logarithmic-ratio and endpoint bounds for minor arcs
-- statement:
--   Put $L=\log((1000/167)2^{1/3})$ and, for $t>0$, define
--
--   $$f(t)=\frac{\frac43\log t-4L+\log3}{\frac{2}{15}t-\frac23\log t+2L}.$$
--
--   Then, uniformly for every positive real $t$,
--
--   $$f(t)\le0.019562618,\qquad 0.27125\log(3+f(t))+0.41415\le0.71392.$$
--
--   These are the logarithmic-ratio estimate (7.38) and its numerical consequence (7.39) in Helfgott's minor-arc argument. Here $1000/167=12/2.004$. Taking $t=\log y$ gives the explicit expression for the endpoint coefficient in (7.37). The theorem does not assert the remaining exponential-sum or sieve estimates.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, Section 7.3, equations (7.37)-(7.39). https://arxiv.org/html/1312.7748v2 . The bound is uniform over all positive t, as stated after (7.38).

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset
open scoped BigOperators

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

theorem Helfgott.minor_arc_logarithmic_ratio_bound (t : ℝ) (ht : 0 < t) :
    let L := Real.log ((1000 / 167 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ))
    let f := ((4 / 3) * Real.log t - (4 * L - Real.log 3)) /
      ((2 / 15) * t - (2 / 3) * Real.log t + 2 * L)
    f ≤ (9781309 / 500000000 : ℝ) ∧
      (217 / 800 : ℝ) * Real.log (3 + f) + (8283 / 20000) ≤ (2231 / 3125) := by sorry
