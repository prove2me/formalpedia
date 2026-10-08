-- Prove2me | Theorems.Thm_KalaiKleitman92_Diameter_recursion
-- name    : KalaiKleitman92.Diameter.recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:03:56.601672+00:00
-- url     : https://prove2.me/theorems/f5350fc2-d372-49f8-a4be-43a69f75f2f7
-- title:
--   p. 2, proof of Theorem 1 — Δ(d, n) ≤ Δ(d − 1, n − 1) + 2Δ(d, [n/2]) + 2, for polyhedra bounded or not
-- statement:
--   Let $P=\{x\in\mathbb R^d : \langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be a polyhedron cut out by $n=k+1$ inequalities with $a_i\ne0$ for every $i$, bounded or not. For a set $F$ of rows write $Q_F$ for the polyhedron obtained from $P$ by ignoring the inequalities outside $F$. Assume
--
--   1. every polyhedron in $\mathbb R^{d-1}$ cut out by $n-1$ inequalities has graph diameter at most $B_1$;
--   2. for every set $F$ of at most $[n/2]$ rows, the graph of $Q_F$ has diameter at most $B_2$.
--
--   Then the graph of $P$ is connected and has diameter at most
--
--   $$B_1+2B_2+2 .$$
--
--   With $B_1=\Delta(d-1,n-1)$ and $B_2=\Delta(d,[n/2])$ this is the inequality $\Delta(d,n)\le\Delta(d-1,n-1)+2\Delta(d,[n/2])+2$ of Kalai and Kleitman, from which the quasi-polynomial bound of Theorem 1 follows by induction.
--
--   **Formalization Note** "At most $n/2$ facets" is a set of rows of cardinality at most $\lfloor n/2\rfloor$. Ignored rows are encoded as the vacuous inequality $\langle 0,x\rangle\le1$. The hypothesis $a_i\ne0$ is needed: a zero row with $b_i=0$ is satisfied with equality everywhere, so two balls could meet only in it, and its "facet" would be all of $P$ rather than a polyhedron of lower dimension; the goal theorem allows zero rows, and its proof removes them first. Connectivity of the graph is not assumed: for polyhedra given by inequalities it is the published `Hirsch.graph_connected_general`. No boundedness is assumed anywhere, in contrast with the published bounded `Hirsch.kalai_kleitman_recursion`.
-- source:
--   Kalai and Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. Amer. Math. Soc. 26 (1992), 315–316 (text of arXiv:math/9204233v1), p. 2, proof of Theorem 1 ("This gives the inequality ∆(d, n) ≤ ∆(d − 1, n − 1) +2∆(d, [n/2]) + 2")

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace KalaiKleitman92.Diameter

open Hirsch

/-- Kalai–Kleitman (1992), p. 2, proof of Theorem 1: "This gives the inequality
Δ(d, n) ≤ Δ(d − 1, n − 1) + 2Δ(d, [n/2]) + 2". Let `P = Hpoly a b ⊆ ℝ^d` be cut out by `n = k + 1`
nonzero inequalities, bounded or not. Suppose every polyhedron in `ℝ^(d-1)` cut out by `k`
inequalities has graph diameter at most `B₁`, and every relaxation of `P` that keeps a set `F` of
at most `[n/2]` rows (the other rows replaced by the vacuous `⟪0, x⟫ ≤ 1`) has graph diameter at
most `B₂`. Then the graph of `P` has diameter at most `B₁ + 2 B₂ + 2`. -/
theorem recursion (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0) (B₁ B₂ : ℕ)
    (IH1 : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B₁)
    (IH2 : ∀ F : Finset (Fin (k + 1)), F.card ≤ (k + 1) / 2 →
      DiamLE (Hpoly (fun i => if i ∈ F then a i else 0)
        (fun i => if i ∈ F then b i else 1)) B₂) :
    DiamLE (Hpoly a b) (B₁ + 2 * B₂ + 2) := by sorry

end KalaiKleitman92.Diameter
