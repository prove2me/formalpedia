-- Prove2me | Theorems.Thm_LocalDOvS_SUS_eq_2
-- name    : LocalDOvS.SUS.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:23.13199+00:00
-- url     : https://prove2.me/theorems/5beec681-4dad-450b-b2c5-dfad947ed6e1
-- title:
--   §3, eq. (2), p.11 — the linear interpolation of a discretely convex function is convex
-- statement:
--   Let $N\ge2$ and let $f$ be discretely convex on $[N]$. Let $\tilde f$ be its linear interpolation. Then:
--
--   1. for every $x_0\in[N-1]$ and $x\in[x_0,x_0+1]$,
--   $$
--   \tilde f(x)=[f(x_0+1)-f(x_0)]\,(x-x_0)+f(x_0);
--   $$
--   2. $\tilde f(n)=f(n)$ for every $n\in[N]$;
--   3. $\tilde f$ is convex on the real interval $[1,N]$;
--   4. for all integers $1\le a\le b\le N$ and every real $x\in[a,b]$ there is an integer $n\in\{a,\dots,b\}$ with $f(n)\le\tilde f(x)$; hence $\min_{\{a,\dots,b\}}f=\min_{[a,b]}\tilde f$.
--
--   This lets the proof of Theorem 2 replace a minimum of $f$ over an integer interval by a minimum of a convex function over a real interval (eq. (EC.14)).
--
--   Differences from the source:
--   - encoding: f̃ defined piecewise on [x₀, x₀+1], x₀ ∈ [N−1] → interp with the piece chosen by ⌊x⌋₊; clause 1 restates (2) on every piece; reason: Lean needs one formula; the pieces agree at shared integers, so it is the same function on [1, N]
--   - generalization: f has a convex linear interpolation on [1, N] → also: f̃ agrees with f on [N], and min over {a,…,b} of f equals min over [a, b] of f̃ (EC.14); reason: the extra clauses are used by the proof of Theorem 2; the statement contains the source's
--   - encoding: min_{x∈{a,…,b}} f(x) = min_{x∈[a,b]} f̃(x) → every value of f̃ on [a, b] is at least some value of f on {a, …, b}; reason: equivalent, since f̃ = f at the integers; avoids a real infimum
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §3, eq. (2), p.11; eq. (EC.14), p.ec16

import Mathlib
import Definitions.Def_LocalDOvS_SUS_DiscConvex
import Definitions.Def_LocalDOvS_SUS_interp

namespace LocalDOvS.SUS

/-- **§3, eq. (2), p.11** (Zhang–Zheng–Lavaei, arXiv:2012.02427v2). If `f` is convex on
`X = [N]`, its linear interpolation `f̃` of (2) is well defined on `[1, N]`, agrees with `f` on
`[N]`, and is convex on `[1, N]`; moreover on every integer interval `[a, b] ⊆ [1, N]` the
minimum of `f̃` over the real interval is attained at an integer (the identity behind (EC.14),
p.ec16: `min_{x ∈ {a, …, b}} f(x) = min_{x ∈ [a, b]} f̃(x)`).

**Formalization Note.** Clause 1 is (2) itself: on each piece `[x₀, x₀ + 1]`, `x₀ ∈ [N − 1]`,
`f̃` is given by the formula of (2) (so the two pieces meeting at an integer agree). The minimum
identity is written "every value of `f̃` on `[a, b]` is at least some value of `f` on
`{a, …, b}`", which avoids a real infimum. -/
theorem eq_2 (N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℝ) (hf : DiscConvex N f) :
    (∀ x₀ ∈ Finset.Icc 1 (N - 1), ∀ x ∈ Set.Icc (x₀ : ℝ) (x₀ + 1),
      interp f x = (f (x₀ + 1) - f x₀) * (x - x₀) + f x₀) ∧
    (∀ n ∈ Finset.Icc 1 N, interp f n = f n) ∧
    ConvexOn ℝ (Set.Icc (1 : ℝ) N) (interp f) ∧
    (∀ a b : ℕ, 1 ≤ a → a ≤ b → b ≤ N →
      ∀ x ∈ Set.Icc (a : ℝ) b, ∃ n ∈ Finset.Icc a b, f n ≤ interp f x) := by sorry

end LocalDOvS.SUS
