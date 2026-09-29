-- Prove2me | Theorems.Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball
-- name    : LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/0493c477-caf9-5d0d-9547-5f27c7cdb2bf
-- title:
--   Landau's theorem on Dirichlet series with non-negative coefficients
-- statement:
--   Let $a : \mathbb{N} \to \mathbb{C}$ be a sequence with $0 \le a$ in the pointwise order induced by the canonical partial order on $\mathbb{C}$, i.e. every $a(n)$ is a non-negative real number. Let $x$ be a real number which is an upper bound for the abscissa of absolute convergence of the $L$-series of $a$, in the sense that $\mathrm{abscissaOfAbsConv}\ a \le x$ as elements of $\overline{\mathbb{R}}$ (so the series $\sum_{n \ge 1} a(n) n^{-s}$ converges absolutely for $\operatorname{Re} s > x$). Suppose given a function $f : \mathbb{C} \to \mathbb{C}$ and a radius $r > 0$ such that $f$ is differentiable on the open ball $B(x, r)$ about the real point $x$ viewed in $\mathbb{C}$, and such that $f(s) = \sum_{n \ge 1} a(n) n^{-s}$ for every $s \in B(x, r)$ with $x < \operatorname{Re} s$. The conclusion is the strict inequality $\mathrm{abscissaOfAbsConv}\ a < x$ in $\overline{\mathbb{R}}$: the $L$-series of $a$ in fact converges absolutely in a half-plane strictly to the left of $\operatorname{Re} s = x$.
--
--   This is Landau's theorem on Dirichlet series with non-negative coefficients, in the contrapositive form: if the series admits a holomorphic extension to a disc centred at a real point $x$ on or to the right of its abscissa of absolute convergence, then that abscissa is strictly smaller than $x$; equivalently, the real point of the line of absolute convergence is a singularity. It is used here to propagate analytic continuation into convergence of Dirichlet series attached to automorphic forms, and to derive a bound on the abscissa of absolute convergence from analyticity at real points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean

import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ComplexOrder
open Complex Set Metric LSeries
namespace LSeries

theorem abscissaOfAbsConv_lt_of_differentiableOn_ball {a : ℕ → ℂ} (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball (x:ℂ) r))
    (hfa : ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s) :
    abscissaOfAbsConv a < x := by sorry
