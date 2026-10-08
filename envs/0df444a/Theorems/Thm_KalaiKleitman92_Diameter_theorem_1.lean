-- Prove2me | Theorems.Thm_KalaiKleitman92_Diameter_theorem_1
-- name    : KalaiKleitman92.Diameter.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:04:07.927501+00:00
-- url     : https://prove2.me/theorems/6894fe43-0a78-4610-bac9-41a05d98acb6
-- title:
--   Theorem 1 — every polyhedron in ℝ^d given by n inequalities, bounded or not, has graph diameter at most n^(log₂ d + 2)
-- statement:
--   Let $P$ be a convex polyhedron. Its **graph** $G(P)$ has the extreme points of $P$ as vertices, and two vertices $u\ne v$ are adjacent when the segment $[u,v]$ is an edge (a one-dimensional face) of $P$; $\delta(P)$ is the diameter of $G(P)$, and $\Delta(d,n)$ is the largest diameter of the graph of a $d$-dimensional polyhedron with $n$ facets.
--
--   **Theorem 1 (Kalai–Kleitman).**
--
--   $$\Delta(d,n)\le n^{\log d+2}.$$
--
--   Stated for polyhedra given by inequalities: for all $d,n\in\mathbb N$, all $a_1,\dots,a_n\in\mathbb R^d$ and $b_1,\dots,b_n\in\mathbb R$, the polyhedron
--
--   $$P=\{x\in\mathbb R^d : \langle a_i,x\rangle\le b_i,\ i=1,\dots,n\},$$
--
--   bounded or not, has a connected graph in which any two vertices are joined by a path of at most $\lfloor n^{\log_2 d+2}\rfloor$ edges.
--
--   This was the first bound on the diameter of polyhedra that is polynomial in $n$ for fixed $d$ and only quasi-polynomial overall. Since $\Delta(d,n)$ is a lower bound on the number of pivots the simplex method needs under any pivot rule, it is also the best known general limit on what a pivot rule could hope to achieve.
--
--   **Formalization Note** The statement is equivalent to (1). A $d$-dimensional polyhedron with $n$ facets is cut out by its $n$ facet inequalities in its affine hull, a copy of $\mathbb R^d$; conversely a polyhedron in $\mathbb R^d$ cut out by $n$ inequalities has dimension $d'\le d$ and at most $n$ facets, and the bound is monotone in $d$ and $n$. The page licenses the inequality reading ("Thus, $P$ is the set of solutions of $n$ linear inequalities in $d$ variables"). "log" is read as $\log_2$ (no base is printed; base $2$ is the one the halving step produces); the power is the real power and the integer bound its floor, which is equivalent because distances are natural numbers. There is no nonemptiness, boundedness, nonzero-row or full-dimensionality hypothesis. Edge cases: $d=0$ ($\mathbb R^0$ is one point; bound $n^2$); $d=1$ ($\log_2 1=0$, bound $n^2$); $n=0$ (bound $0$ for $d\ge1$, where $P=\mathbb R^d$ has no vertex); polyhedra without vertices satisfy the statement vacuously. "Diameter at most $B$" includes connectivity: it is the published `Hirsch.DiamLE`, a walk of exactly $B$ steps each of which stays put or crosses an edge. The bounded case is the published `Hirsch.kalai_kleitman_bound`; this statement drops its nonemptiness and boundedness hypotheses, as the paper does.
-- source:
--   Kalai and Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. Amer. Math. Soc. 26 (1992), 315–316 (text of arXiv:math/9204233v1), p. 2, Theorem 1, display (1); definitions of G(P), δ(P), Δ(d, n) on p. 1

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace KalaiKleitman92.Diameter

open Hirsch

/-- Kalai–Kleitman (1992), p. 2, Theorem 1, display (1): `Δ(d, n) ≤ n ^ (log d + 2)`. Every
polyhedron `P = {x ∈ ℝ^d | ⟪a i, x⟫ ≤ b i for all i < n}` cut out by `n` linear inequalities,
bounded or not, has a connected vertex–edge graph of diameter at most `⌊n ^ (log₂ d + 2)⌋`. -/
theorem theorem_1 (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    DiamLE (Hpoly a b) ⌊(n : ℝ) ^ (Real.logb 2 (d : ℝ) + 2)⌋₊ := by sorry

end KalaiKleitman92.Diameter
