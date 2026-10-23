-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_corollary_5_6
-- name    : NonconvexCost.Complexity.corollary_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:48.546798+00:00
-- url     : https://prove2.me/theorems/bd650fe1-8ee0-4c25-a59c-712a1296ed74
-- title:
--   Corollary 5.6, p. 13 (line search complexity) — bisection terminates within 1 + ⌊2M/σ⌋ evaluations
-- statement:
--   Let $p<q$ and let $h\colon[p,q]\to\mathbb R$ have a finite right derivative $h'_+$ at every point of $[p,q)$, finite concave deviation $M$ on $[p,q]$, and average rate of decrease
--   $$\sigma=-\frac{h(q)-h(p)}{q-p}>0 .$$
--   Then the number of evaluations of $h'_+$ required before the bisection method, Algorithm 3.1, terminates is no more than
--   $$1+\Big\lfloor\frac{2M}{\sigma}\Big\rfloor ;$$
--   that is, among the first $1+\lfloor 2M/\sigma\rfloor$ evaluations at least one is negative.
--
--   This is the univariate complexity bound that, applied on segments of length $\delta$, gives the cost of each line search in Algorithm 4.1.
--
--   **Formalization Note** The existence of the finite right derivative on $[p,q)$ is added so that the evaluated values are real numbers.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 13, Corollary 5.6

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting

namespace NonconvexCost.Complexity

open Set

theorem corollary_5_6 (h h' : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hder : IsRightDerivOn h h' p q)
    (hM : concaveDeviation h (Icc p q) ≠ ⊤) (hσ : 0 < -((h q - h p) / (q - p))) :
    ¬ NoStopWithin h h' p q
      (1 + ⌊2 * (concaveDeviation h (Icc p q)).toReal / (-((h q - h p) / (q - p)))⌋₊) := by sorry

end NonconvexCost.Complexity
