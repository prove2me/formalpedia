-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_eq_1_12_1_13
-- name    : KurtzProtter91.Integrals.eq_1_12_1_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:20.902996+00:00
-- url     : https://prove2.me/theorems/c66501d9-84a8-4f98-b098-4fd56edc9feb
-- title:
--   (1.12)–(1.13) — integrals against uniformly finitely-jumping step functions converge (quadruple in D_{ℝ⁴})
-- statement:
--   Let $x_n,y_n,x,y$ be real cadlag paths. Suppose each $y_n$ is piecewise constant, and the number of discontinuities of $y_n$ in a bounded time interval is uniformly bounded in $n$: for every $T$ there is $K$ with at most $K$ jumps of $y_n$ in $[0,T]$ for all $n$. Suppose $(x_n,y_n)\to(x,y)$ in the Skorohod topology on $D_{\mathbb R^2}[0,\infty)$. Let
--   $$I_n=\int_0^\cdot x_n(s-)\,dy_n(s),\quad J_n=\int_0^\cdot y_n(s-)\,dx_n(s),\quad I=\int_0^\cdot x(s-)\,dy(s),\quad J=\int_0^\cdot y(s-)\,dx(s),$$
--   each the limit of left-point Riemann sums (1.7). Then the quadruple converges:
--   $$(x_n,y_n,I_n,J_n)\to(x,y,I,J)\quad\text{in the Skorohod topology on }D_{\mathbb R^4}[0,\infty).$$
--   In particular (1.12) $\int_0^\cdot x_n(s-)\,dy_n(s)\to\int_0^\cdot x(s-)\,dy(s)$ and (1.13) $\int_0^\cdot y_n(s-)\,dx_n(s)\to\int_0^\cdot y(s-)\,dx(s)$ in $D_{\mathbb R}[0,\infty)$.
--
--   This is the deterministic core of Theorem 2.2: once the integrand is replaced by a step function, the integrals converge.
--
--   **Formalization Note** The statement formalizes the paper's parenthetical "the quadruple consisting of $x_n$, $y_n$ and the two integrals converges in $D_{\mathbb R^4}[0,\infty)$", which implies (1.12) and (1.13) and is the form the proof of Theorem 2.2 uses. The four integrals are given processes characterized by the pathwise Riemann-sum limit; such limits exist when the integrator or the integrand is a step path, and the limit $y$ of the $y_n$ is again a step path (it is not assumed to be). The jump count bound is stated with `Set.ncard` of the (finite) set of jump times in $[0,T]$.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1038, Section 1, (1.12)–(1.13)

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open Filter Topology
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem eq_1_12_1_13 (xs ys Is Js : ℕ → ℝ≥0 → ℝ) (x y I J : ℝ≥0 → ℝ)
    (hys : ∀ n, IsStepPath (ys n))
    (hbound : ∀ T : ℝ≥0, ∃ K : ℕ, ∀ n, (jumpTimes (ys n) T).ncard ≤ K)
    (hconv : SkorohodTendsto (fun n t => (xs n t, ys n t)) (fun t => (x t, y t)))
    (hIs : ∀ n, HasLeftIntegralR (xs n) (ys n) (Is n))
    (hJs : ∀ n, HasLeftIntegralR (ys n) (xs n) (Js n))
    (hI : HasLeftIntegralR x y I) (hJ : HasLeftIntegralR y x J) :
    SkorohodTendsto (fun n t => (xs n t, ys n t, Is n t, Js n t)) (fun t => (x t, y t, I t, J t)) := by sorry

end KurtzProtter91.Integrals
