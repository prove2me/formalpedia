-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_theorem_5_2
-- name    : NonconvexCost.Complexity.theorem_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:48.34725+00:00
-- url     : https://prove2.me/theorems/bf4a4dc6-de4a-4726-a709-b9344419fada
-- title:
--   Theorem 5.2, p. 11 — k ≥ 1 non-terminating bisection evaluations force (h(q) − h(p))/(q − p) ≥ (s′₊(p) − s′₋(q))/k
-- statement:
--   Let $p<q$ and $h,s\colon[p,q]\to\mathbb R$ with $s$ convex and $h+s$ convex on $[p,q]$. Suppose $h$ has a finite right derivative $h'_+(t)$ at every $t\in[p,q)$, and $s$ has finite right derivative $s'_+(p)$ at $p$ and left derivative $s'_-(q)$ at $q$. If the bisection method, Algorithm 3.1, evaluates $h'_+$ $k\ge1$ times without terminating (the first $k$ evaluations, at $p$ and then at the successive midpoints, are all nonnegative), then
--   $$\frac{h(q)-h(p)}{q-p}\ \ge\ \frac{s'_+(p)-s'_-(q)}{k}.$$
--
--   Thus if $h$ decreases on average over $[p,q]$, the number of evaluations before termination is bounded by the variation of the derivative of a convexifying perturbation.
--
--   **Formalization Note** The finiteness of the one-sided derivatives is added (the page writes them without comment). The bisection keeps $[l,m]$ when $2h(m)<h(l)+h(r)$, as in (5.3).
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 11, Theorem 5.2

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting

namespace NonconvexCost.Complexity

open Set

theorem theorem_5_2 (h h' s : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hs : ConvexOn ℝ (Icc p q) s)
    (hhs : ConvexOn ℝ (Icc p q) (h + s)) (hder : IsRightDerivOn h h' p q) (sp sq : ℝ)
    (hsp : HasDerivWithinAt s sp (Icc p q) p) (hsq : HasDerivWithinAt s sq (Icc p q) q)
    (k : ℕ) (hk : 1 ≤ k) (hrun : NoStopWithin h h' p q k) :
    (sp - sq) / k ≤ (h q - h p) / (q - p) := by sorry

end NonconvexCost.Complexity
