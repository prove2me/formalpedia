-- Prove2me | Theorems.Thm_LinearChoresCLS_epsKKT_iff_approx_of_negated_quadratic
-- name    : LinearChoresCLS.epsKKT_iff_approx_of_negated_quadratic
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:23:41.891909+00:00
-- url     : https://prove2.me/theorems/1027bdda-d446-482e-8586-ec05ee48c6ba
-- title:
--   Maximization $\varepsilon$-KKT is minimization $\varepsilon$-KKT for $-Q$
-- statement:
--   Let $Q(x)=\frac12x^\top Ax+c^\top x$ and let $Q'(x)=-Q(x)$ be the quadratic obtained by negating every entry of $A$ and $c$. For $\varepsilon\ge0$ and $x\in\mathbb R^n$, the point $x$ satisfies the maximization $\varepsilon$-KKT conditions of Definition 2.4 for $Q$ if and only if it satisfies the minimization $\varepsilon$-KKT conditions for $Q'$:
--   \[
--   x_i=0\Rightarrow \partial_iQ(x)\le\varepsilon,\qquad
--   0<x_i<1\Rightarrow|\partial_iQ(x)|\le\varepsilon,\qquad
--   x_i=1\Rightarrow\partial_iQ(x)\ge-\varepsilon
--   \]
--   is equivalent to $x\in[0,1]^n$, $\partial_iQ'(x)\le\varepsilon$ when $x_i>0$, and $\partial_iQ'(x)\ge-\varepsilon$ when $x_i<1$.
--
--   This sign-conversion lemma connects `LinearChoresCLS.IsEpsKKT` with the public `NetworkEquilibriumCLS.LinearNash.ApproxQuadraticKKT`; it is necessary before applying the latter's rounding results to the chores reduction.
--
--   **Formalization Note** The hypotheses assert coefficientwise that $P'$ encodes $-P$; consequently `sourceGradient P' x i = -sourceGradient P x i`.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, arXiv:2611.06589 (held version sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Definition 2.4 and Eq. (2.6), p.7; sign conversion with Anagnostides–Panageas–Yan, STOC 2027 #653, Definition 2.1, printed p.6 (PDF 7).

import Mathlib
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash

theorem LinearChoresCLS.epsKKT_iff_approx_of_negated_quadratic {n : ℕ} (P P' : NetworkEquilibriumCLS.LinearNash.Quadratic n)
    (hQ : ∀ i j, P'.Q i j = -P.Q i j) (hc : ∀ i, P'.c i = -P.c i)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Fin n → ℝ) :
    IsEpsKKT P ε x ↔ NetworkEquilibriumCLS.LinearNash.ApproxQuadraticKKT P' ε x := by sorry
