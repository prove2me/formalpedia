-- Prove2me | Theorems.Thm_LocalDOvS_SUS_case_I
-- name    : LocalDOvS.SUS.case_I
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:55.905623+00:00
-- url     : https://prove2.me/theorems/372b4afa-3dbd-430e-9ac0-b4655e03e309
-- title:
--   Case I, p.ec15 — a Type-I Operation discards only points no better than $x$
-- statement:
--   Let $f$ be discretely convex on $[N]$ and let $x,y\in[N]$ with $f(x)\le f(y)$.
--
--   1. If $x<y$, then for every $z\in[N]$ with $z\ge y$,
--   $$
--   f(z)\ge f(y)\ge f(x).
--   $$
--   2. If $y<x$, then for every $z\in[N]$ with $z\le y$, $f(z)\ge f(y)\ge f(x)$.
--
--   In the proof of Theorem 2, a Type-I Operation on $x,y$ with $f(x)\le f(y)$ removes exactly such points $z$, so it discards nothing better than $x$, and neither the best value on the active set nor the global minimum over the interval is lost.
--
--   Differences from the source:
--   - encoding: Case I argued on the event f(x) ≤ f(y) → f x ≤ f y as a hypothesis; reason: this is the convexity step of Case I; the event is supplied by good_event
--   - encoding: If y < x, the proof is the same → the mirror case stated as a second clause; reason: the source asserts it; stated explicitly
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, proof of Theorem 2, Case I, p.ec15

import Mathlib
import Definitions.Def_LocalDOvS_SUS_DiscConvex

namespace LocalDOvS.SUS

/-- **Case I of the proof of Theorem 2, p.ec15** (Zhang–Zheng–Lavaei, arXiv:2012.02427v2). Let
`f` be convex on `[N]` and `x, y ∈ [N]` with `f(x) ≤ f(y)`. If `x < y`, then
`f(z) ≥ f(y) ≥ f(x)` for every `z ∈ [N]` with `z ≥ y`; symmetrically ("If `y < x`, the proof is
the same"), if `y < x`, then `f(z) ≥ f(y) ≥ f(x)` for every `z ∈ [N]` with `z ≤ y`. So a
Type-I Operation only discards points whose value is at least `f(x)`. -/
theorem case_I (N : ℕ) (f : ℕ → ℝ) (hf : DiscConvex N f) (x y : ℕ)
    (hx : x ∈ Finset.Icc 1 N) (hy : y ∈ Finset.Icc 1 N) (hxy : f x ≤ f y) :
    (x < y → ∀ z ∈ Finset.Icc 1 N, y ≤ z → f y ≤ f z ∧ f x ≤ f y) ∧
    (y < x → ∀ z ∈ Finset.Icc 1 N, z ≤ y → f y ≤ f z ∧ f x ≤ f y) := by sorry

end LocalDOvS.SUS
