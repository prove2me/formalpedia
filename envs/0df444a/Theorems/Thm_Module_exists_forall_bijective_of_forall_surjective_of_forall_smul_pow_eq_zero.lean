-- Prove2me | Theorems.Thm_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
-- name    : Module.exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/d12e6c50-63dc-5d4b-8082-6e4ba3e7d500
-- title:
--   Chain of surjections of torsion modules over a DVR eventually bijective
-- statement:
--   Let $R$ be a commutative ring that is a domain and a discrete valuation ring, let $\varpi \in R$ be an element whose span is the maximal ideal of $R$ (so $\varpi$ is a uniformiser), and let $H : \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules equipped with $R$-linear maps $\varphi_n : H_n \to H_{n+1}$ for every $n$, each assumed surjective. Suppose there is an index $N$ such that for all $n \ge N$ the module $H_n$ is finite (finitely generated) over $R$ and, for each such $n$, some power $\varpi^{k}$ (with $k$ allowed to depend on $n$) annihilates every element of $H_n$. The conclusion is the existence of an index $n_0$ such that for all $n \ge n_0$ the map $\varphi_n$ is bijective. Nothing is asserted about $\varphi_n$ for $n$ below the threshold, and the threshold produced is not claimed to be $N$ itself.
--
--   This is the standard stabilisation principle for a tower of surjections between finitely generated modules of finite length over a discrete valuation ring: once lengths cease to drop, the surjections become isomorphisms. It is used in the construction of two-chart integral models of algebraic curves, where the $H_n$ arise as cohomology groups of a tower of twisting sheaves, in [`AlgebraicCurve.TwoChartIntegralModel.exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData`](thm.html#AlgebraicCurve.TwoChartIntegralModel.exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Module.exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (H : ℕ → Type v) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
    (φ : ∀ n, H n →ₗ[R] H (n + 1)) (hφ : ∀ n, Function.Surjective (φ n))
    (N : ℕ) (hfin : ∀ n, N ≤ n → Module.Finite R (H n))
    (htors : ∀ n, N ≤ n → ∃ k : ℕ, ∀ x : H n, ϖ ^ k • x = 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Function.Bijective (φ n) := by sorry
