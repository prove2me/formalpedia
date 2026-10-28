-- Prove2me | Theorems.Thm_MonotoneOn_of_hasDerivAt_nonneg
-- name    : MonotoneOn.of_hasDerivAt_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T16:29:21.458752+00:00
-- url     : https://prove2.me/theorems/9b62bc6d-12d2-455c-9353-1c8f74cf4b6e
-- title:
--   A nonnegative derivative on a closed interval makes the function monotone there
-- statement:
--   Let $f,g\colon\mathbb R\to\mathbb R$ and let $a\le b$ be real. Suppose that at every point
--   $x$ of the closed interval $[a,b]$ the function $f$ is differentiable with derivative $g(x)$,
--   and that
--
--   $$
--   0 \;\le\; g(x) \qquad \text{for every } x\in[a,b].
--   $$
--
--   Then $f$ is monotone increasing on $[a,b]$: $f(x)\le f(y)$ whenever $x\le y$ both lie in
--   $[a,b]$.
--
--   The hypothesis is deliberately the convenient one. Mathlib's interval monotonicity lemmas ask
--   for continuity on the closed interval together with a derivative condition on its interior, so
--   using them means producing `ContinuousOn` and `DifferentiableOn` facts and then restricting to
--   `interior (Icc a b)`. In practice a proof has already established `HasDerivAt f (g x) x` at
--   every point of the closed interval — that is what differentiating an explicit formula gives —
--   and wants the conclusion directly. This is the step behind every "the objective is increasing
--   in the price", "the value function is nondecreasing in the threshold" or "the bound tightens
--   along the interval" argument. Five accepted proofs in this collection each do the plumbing
--   separately.
--
--   **Formalization Note.** `hd` is `HasDerivAt f (g x) x` for `x ∈ Icc a b`, pointwise on the
--   *closed* interval, and `hg` is `0 ≤ g x` on the same set. No continuity or differentiability
--   hypothesis is needed beyond `hd`, and `a ≤ b` is not assumed: when `b < a` the interval is
--   empty and the conclusion is vacuous.
-- source:
--   Five distinct accepted submissions prove this inline, each for itself. Carved from https://prove2.me/submissions/108d25ac-4cbb-466b-9bd4-122188ee844b, lines 83-93.

import Mathlib

open Set

theorem MonotoneOn.of_hasDerivAt_nonneg {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) : MonotoneOn f (Icc a b) := by sorry
