-- Prove2me | Theorems.Thm_IsPreconnected_exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent
-- name    : IsPreconnected.exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/35403a13-f131-54a6-8b92-50500bbbf1f9
-- title:
--   Integer coordinates in a varying frame are locally constant
-- statement:
--   Let $X$ be a topological space, $V$ a finite-dimensional real normed vector space, $k$ a natural number and $S \subseteq X$ a preconnected subset. Suppose given maps $v_i : X \to V$, indexed by $i \in \mathrm{Fin}\,k$, each continuous on $S$, such that for every $z \in S$ the family $(v_i(z))_{i}$ is linearly independent over $\mathbb{R}$; and a map $x : X \to V$, continuous on $S$, such that for every $z \in S$ there exists an integer vector $n \in \mathbb{Z}^{\mathrm{Fin}\,k}$ with $x(z) = \sum_i n_i \cdot v_i(z)$ (integer scalar multiplication on $V$). The conclusion is that a single integer vector works uniformly: there exists $n \in \mathbb{Z}^{\mathrm{Fin}\,k}$ such that $x(z) = \sum_i n_i \cdot v_i(z)$ for all $z \in S$. Note that the integrality hypothesis is assumed pointwise on $S$, with no a priori coherence between the coordinate vectors at different points, and that $S$ is only assumed preconnected (the empty set being allowed, in which case the statement is vacuous and any $n$ serves).
--
--   This is the rigidity of discrete data in a continuously varying frame: a vector lying in the lattice spanned by a continuously varying linearly independent family has locally constant, hence (on a preconnected set) globally constant, integer coordinates. It is used in the Čerednik–Drinfeld part of the development, to show that the frame coordinates of a uniformising family of fake elliptic curves are constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsPreconnected_exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsPreconnected.exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent
    {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {k : ℕ} {S : Set X} (hS : IsPreconnected S)
    (v : Fin k → X → V) (hv : ∀ i, ContinuousOn (v i) S)
    (hlin : ∀ z ∈ S, LinearIndependent ℝ (fun i => v i z))
    (x : X → V) (hx : ContinuousOn x S)
    (hmem : ∀ z ∈ S, ∃ n : Fin k → ℤ, x z = ∑ i, n i • v i z) :
    ∃ n : Fin k → ℤ, ∀ z ∈ S, x z = ∑ i, n i • v i z := by sorry
