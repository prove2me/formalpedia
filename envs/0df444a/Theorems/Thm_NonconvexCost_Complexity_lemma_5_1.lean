-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_lemma_5_1
-- name    : NonconvexCost.Complexity.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:08.858131+00:00
-- url     : https://prove2.me/theorems/4aecbaa0-0cce-4749-beab-0e302624c7cd
-- title:
--   Lemma 5.1, p. 11 — if h′₊(x) ≥ 0 then (h(y) − h(x))/(y − x) ≥ s′₊(x) − s′₋(y)
-- statement:
--   Let $p\le x<y\le q$, and let $h,s\colon[p,q]\to\mathbb R$ with $s$ convex and $h+s$ convex on $[p,q]$. Suppose $h$ has a right derivative $h'_+(x)\ge0$ at $x$, $s$ has right derivative $s'_+(x)$ at $x$ and left derivative $s'_-(y)$ at $y$ (all finite). Then
--   $$\frac{h(y)-h(x)}{y-x}\ \ge\ s'_+(x)-s'_-(y).$$
--
--   This is the base estimate of the line-search analysis: a convex perturbation $s$ that convexifies $h$ controls how fast $h$ can decrease after a point where the bisection did not stop.
--
--   **Formalization Note** The one-sided derivatives are real numbers supplied with `HasDerivWithinAt` on $[x,q]$ (right) and $[p,y]$ (left); their existence is an added hypothesis making the page's $h'_+(x)$, $s'_+(x)$, $s'_-(y)$ finite.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 11, Lemma 5.1

import Mathlib

namespace NonconvexCost.Complexity

open Set

theorem lemma_5_1 (h s : ℝ → ℝ) (p q : ℝ) (hs : ConvexOn ℝ (Icc p q) s)
    (hhs : ConvexOn ℝ (Icc p q) (h + s)) (x y : ℝ) (hpx : p ≤ x) (hxy : x < y) (hyq : y ≤ q)
    (c a b : ℝ) (hc : HasDerivWithinAt h c (Icc x q) x) (hc0 : 0 ≤ c)
    (ha : HasDerivWithinAt s a (Icc x q) x) (hb : HasDerivWithinAt s b (Icc p y) y) :
    a - b ≤ (h y - h x) / (y - x) := by sorry

end NonconvexCost.Complexity
