-- Prove2me | Theorems.Thm_GenEmpLik_Expansion_eq_30
-- name    : GenEmpLik.Expansion.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:25:41.982995+00:00
-- url     : https://prove2.me/theorems/5f80aefd-e0ff-4c13-8b34-8d2a788bf40c
-- title:
--   (30) — the Huber/quadratic sandwich $2(1-C\epsilon)h_\epsilon(t)\le f(t+1)\le(1+C\epsilon)t^2$
-- statement:
--   Let $f$ satisfy Assumption A. There exist constants $0<c,C<\infty$, depending only on $f$, such that for every $\epsilon$ with $0<\epsilon\le c$:
--
--   1. for every $t\ge-1$,
--   $$
--   2(1-C\epsilon)\,h_\epsilon(t)\le f(t+1);
--   $$
--   2. for every $t$ with $|t|\le\epsilon$,
--   $$
--   f(t+1)\le(1+C\epsilon)\,t^2 .
--   $$
--
--   Here $h_\epsilon$ is the Huber function. The sandwich compares the divergence ball with a quadratic (χ²) ball from inside and a Huber ball from outside, which is how the robust mean is reduced to the sample variance.
--
--   **Formalization Note** The paper writes the upper bound as $f(t+1)\le(1+C\epsilon)t^2+\mathbf I_{[-\epsilon,\epsilon]}(t)$ "for all $t\in\mathbb R$"; with the convex indicator $\mathbf I$ ($0$ on the interval, $+\infty$ off it) this is exactly clause 2. The lower bound is stated for $t\ge-1$, the arguments at which $f(t+1)$ is defined. "$|\epsilon|\le c$" is read as $0<\epsilon\le c$, since $h_\epsilon$ is defined for $\epsilon>0$ only. Values of $f$ are in `EReal`.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 32, App. A.1, (30)

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Definitions.Def_GenEmpLik_Expansion_huber

namespace GenEmpLik.Expansion

/-- (30) (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 32): under Assumption A there are
constants `0 < c, C < ∞`, depending only on `f`, such that for every `0 < ε ≤ c`
`2(1 − Cε) h_ε(t) ≤ f(t + 1)` for all `t ≥ −1`, and `f(t + 1) ≤ (1 + Cε) t²` for `|t| ≤ ε`.
The paper's `+ I_{[−ε,ε]}(t)` is the `{0, +∞}` indicator, so the upper bound is only a
constraint for `|t| ≤ ε`; `f(t + 1)` is only defined for `t ≥ −1`. -/
theorem eq_30 (f : ℝ → EReal) (hA : AssumptionA f) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ c →
      (∀ t : ℝ, -1 ≤ t → ((2 * (1 - C * ε) * huber ε t : ℝ) : EReal) ≤ f (t + 1)) ∧
      (∀ t : ℝ, |t| ≤ ε → f (t + 1) ≤ (((1 + C * ε) * t ^ 2 : ℝ) : EReal)) := by sorry

end GenEmpLik.Expansion
