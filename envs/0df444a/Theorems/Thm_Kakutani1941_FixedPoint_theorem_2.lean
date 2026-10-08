-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_theorem_2
-- name    : Kakutani1941.FixedPoint.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:03:10.678395+00:00
-- url     : https://prove2.me/theorems/c406e3eb-6155-4939-9fd6-e0b729a2d830
-- title:
--   Theorem 2 — von Neumann's intersection theorem
-- statement:
--   Let $K\subseteq\mathbb R^m$ and $L\subseteq\mathbb R^n$ be bounded closed convex sets, with $K$ nonempty, and consider their Cartesian product $K\times L\subseteq\mathbb R^m\times\mathbb R^n$. Let $U$ and $V$ be closed subsets of $K\times L$ such that
--
--   1. for every $x_0\in K$ the section $U_{x_0}=\{y\in L:(x_0,y)\in U\}$ is nonempty, closed and convex, and
--   2. for every $y_0\in L$ the section $V_{y_0}=\{x\in K:(x,y_0)\in V\}$ is nonempty, closed and convex.
--
--   Then $U$ and $V$ have a common point:
--
--   $$U\cap V\neq\emptyset.$$
--
--   Kakutani attributes this theorem to J. von Neumann's 1937 paper on an economic equilibrium system, where it was proved by other means, and derives it from the Corollary to Theorem 1. The paper's Theorem 3, the minimax theorem for quasi-convex–quasi-concave continuous functions, follows from it.
--
--   **Formalization Note** The page writes the intersection as $U\cdot V$ (1941 notation) and says "$U$ and $V$ have a common point". The hypothesis $K\neq\emptyset$ is added: if $K=\emptyset$ then condition 2 forces $L=\emptyset$, so $U=V=\emptyset$ and the conclusion fails; $L\neq\emptyset$ then follows from condition 1. The page's product "$K\times L$ in $R^{m+n}$" is the product of the Euclidean spaces $\mathbb R^m\times\mathbb R^n$ with the product topology, which is the topology of $\mathbb R^{m+n}$. Sections are taken inside $L$ and $K$ as the page writes them.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 458, Theorem 2, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib

namespace Kakutani1941.FixedPoint

/-- Theorem 2, p. 458: von Neumann's intersection theorem. The page writes `U · V` for `U ∩ V`. -/
theorem theorem_2 {m n : ℕ} {K : Set (EuclideanSpace ℝ (Fin m))}
    {L : Set (EuclideanSpace ℝ (Fin n))}
    (hKbounded : Bornology.IsBounded K) (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (hKnonempty : K.Nonempty)
    (hLbounded : Bornology.IsBounded L) (hLclosed : IsClosed L) (hLconvex : Convex ℝ L)
    (U V : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (hUclosed : IsClosed U) (hVclosed : IsClosed V)
    (hUsub : U ⊆ K ×ˢ L) (hVsub : V ⊆ K ×ˢ L)
    (hUsec : ∀ x₀ ∈ K,
      {y | y ∈ L ∧ (x₀, y) ∈ U}.Nonempty ∧ IsClosed {y | y ∈ L ∧ (x₀, y) ∈ U} ∧
        Convex ℝ {y | y ∈ L ∧ (x₀, y) ∈ U})
    (hVsec : ∀ y₀ ∈ L,
      {x | x ∈ K ∧ (x, y₀) ∈ V}.Nonempty ∧ IsClosed {x | x ∈ K ∧ (x, y₀) ∈ V} ∧
        Convex ℝ {x | x ∈ K ∧ (x, y₀) ∈ V}) :
    (U ∩ V).Nonempty := by sorry

end Kakutani1941.FixedPoint
