-- Prove2me | Theorems.Thm_KalaiKleitman92_Diameter_ball_radius_le
-- name    : KalaiKleitman92.Diameter.ball_radius_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:03:37.390977+00:00
-- url     : https://prove2.me/theorems/997b7521-2e7c-4bbb-b0e0-7fdce59f480b
-- title:
--   p. 2, proof of Theorem 1 — k_v ≤ Δ(d, [n/2]): inside a ball touching only the rows of F, distances from v are bounded by the diameter of the relaxation to F
-- statement:
--   Let $P=\{x\in\mathbb R^d : \langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be a polyhedron, bounded or not, and let $G(P)$ be its graph: the vertices are the extreme points of $P$, and two vertices $u\ne v$ are adjacent when the segment $[u,v]$ is an edge (an extreme subset) of $P$. For a set $F\subseteq\{1,\dots,n\}$ of rows let
--
--   $$Q_F=\{x\in\mathbb R^d : \langle a_i,x\rangle\le b_i \text{ for all } i\in F\}$$
--
--   be the polyhedron obtained from $P$ by ignoring every inequality outside $F$.
--
--   Fix a vertex $v$ of $P$ and a radius $k\in\mathbb N$, and assume that every vertex of $P$ at distance at most $k$ from $v$ in $G(P)$ satisfies with equality only inequalities with index in $F$. If every two vertices of $Q_F$ are at distance at most $B$ in $G(Q_F)$, then every vertex $\omega$ of $P$ at distance at most $k$ from $v$ in $G(P)$ is at distance at most $B$ from $v$ in $G(P)$:
--
--   $$\operatorname{dist}_{G(P)}(v,\omega)\le k \;\Longrightarrow\; \operatorname{dist}_{G(P)}(v,\omega)\le B .$$
--
--   This is the claim "$k_v\le\Delta(d,[n/2])$" of Kalai and Kleitman, which they derive from the inner claim "the distance of $\omega$ from $v$ in $G(Q)$ is also $k_v$". In their proof $F$ is the set of facets met by the ball of radius $k_v$ around $v$; it has at most $n/2$ elements, so $Q_F$ is a polyhedron with at most $[n/2]$ facets and its diameter is at most $\Delta(d,[n/2])$. Hence every vertex of the ball is within $\Delta(d,[n/2])$ of $v$.
--
--   **Formalization Note** The paper's $k_v$ ("the maximal positive number such that …") need not exist: no radius qualifies when $v$ itself lies on more than $n/2$ facets, and every radius qualifies when no ball ever meets more than $n/2$ facets. The statement therefore quantifies over any radius $k$ with the ball property, and states the conclusion as a distance bound inside the ball, which is what the recursion uses. No bound on $|F|$ is needed here; it enters through the recursion's hypothesis on relaxations. Ignored rows are encoded as the vacuous inequality $\langle 0,x\rangle\le 1$, which keeps $n$ rows. "Distance at most $k$" is a walk of exactly $k$ steps in which each step stays put or crosses an edge (the `DiamLE` convention of the published `Hirsch_model`). No boundedness is assumed.
-- source:
--   Kalai and Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. Amer. Math. Soc. 26 (1992), 315–316 (text of arXiv:math/9204233v1), p. 2, proof of Theorem 1 ("We claim now that kv ≤ ∆(d, [n/2])" and "We claim that the distance of ω from v in G(Q) is also kv")

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace KalaiKleitman92.Diameter

open Hirsch

/-- Kalai–Kleitman (1992), p. 2, proof of Theorem 1: "We claim now that k_v ≤ Δ(d, [n/2])",
through "the distance of ω from v in G(Q) is also k_v". Let `v` be a vertex of
`P = Hpoly a b`, let `k` be a radius such that every vertex of `P` reachable from `v` by a walk
of (at most) `k` steps has all its tight rows in `F`, and let `Q` be `P` with every row outside
`F` replaced by the vacuous `⟪0, x⟫ ≤ 1`. If the graph of `Q` has diameter at most `B`, then every
vertex `ω` of `P` reachable from `v` in at most `k` steps is reachable from `v` in at most `B`
steps of the graph of `P`. Walks have exactly the stated number of steps; a step stays put or
crosses an edge, so "`k` steps" means "at most `k` edges". -/
theorem ball_radius_le (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) (k B : ℕ) (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hball : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = v ∧ w k = x ∧
        ∀ j < k, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) →
      ∀ i, ⟪a i, x⟫ = b i → i ∈ F)
    (hQ : DiamLE (Hpoly (fun i => if i ∈ F then a i else 0)
      (fun i => if i ∈ F then b i else 1)) B)
    (ω : EuclideanSpace ℝ (Fin d)) (hω : ω ∈ Set.extremePoints ℝ (Hpoly a b))
    (hωk : ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = v ∧ w k = ω ∧
      ∀ j < k, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = v ∧ w B = ω ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end KalaiKleitman92.Diameter
