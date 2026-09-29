-- Prove2me | Theorems.Thm_Module_exists_basis_padicValRat_apply_nonneg_iff_pair
-- name    : Module.exists_basis_padicValRat_apply_nonneg_iff_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/dfcd6118-d1d2-5bb0-8868-811163fe3f20
-- title:
--   Adapted basis for a nested pair of p-integral lattices
-- statement:
--   Let $p$ be a prime and let $M$ be a finite-dimensional vector space over $\mathbb{Q}$. Given two families $a, a' : \mathbb{Z} \to (M \to_{\mathbb{Q}} \mathbb{Q})$ of linear functionals on $M$, assume: the family $a'$ separates points, i.e. any $x$ with $a'_m x = 0$ for all $m$ is zero; both families have uniformly bounded denominators, i.e. for each $x$ there is $N \in \mathbb{N}$ with $v_p(p^N a_m x) \ge 0$ for all $m$, and likewise for $a'$; and every $a$-integral vector is $a'$-integral, i.e. $v_p(a_m x) \ge 0$ for all $m$ implies $v_p(a'_m x) \ge 0$ for all $m$ (here $v_p$ is `padicValRat`, with the convention $v_p(0) = 0$, so vanishing values are integral). Assume further that $u \in M$ satisfies $v_p(a_m u) \ge 0$ for all $m$, and that $a'_{m} u \neq 0$ with $v_p(a'_{m} u) = 0$ for some $m$. The conclusion asserts the existence of $n \in \mathbb{N}$, a $\mathbb{Q}$-basis $b$ of $M$ indexed by $\mathrm{Fin}\,n$, exponents $e : \mathrm{Fin}\,n \to \mathbb{N}$ and an index $i_0$ such that $b_{i_0} = u$, $e_{i_0} = 0$, and for every coordinate vector $c : \mathrm{Fin}\,n \to \mathbb{Q}$, writing $x = \sum_i c_i b_i$: $v_p(a_m x) \ge 0$ for all $m$ if and only if $v_p(c_i) \ge 0$ for all $i$, and $v_p(a'_m x) \ge 0$ for all $m$ if and only if $v_p(c_i) \ge -e_i$ for all $i$.
--
--   This is the Smith normal form (elementary divisor) statement for the inclusion of the lattice of $a$-integral vectors into the lattice of $a'$-integral vectors over the discrete valuation ring $\mathbb{Z}_{(p)}$, in the refined form where a prescribed vector $u$, primitive for the larger lattice, is taken as one of the basis vectors and has elementary divisor exponent $0$. It is used in the construction of the family contexts for multiplicative coverings of modular curves, via [`ModularCurve.MultCovering.exists_famCtx`](thm.html#ModularCurve.MultCovering.exists_famCtx) and [`ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue`](thm.html#ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_basis_padicValRat_apply_nonneg_iff_pair.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.exists_basis_padicValRat_apply_nonneg_iff_pair
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M] (p : ℕ) [Fact p.Prime]
    (a a' : ℤ → M →ₗ[ℚ] ℚ) (hinj' : ∀ x, (∀ m, a' m x = 0) → x = 0)
    (hbd : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a m x))
    (hbd' : ∀ x, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a' m x))
    (hsub : ∀ x, (∀ m, 0 ≤ padicValRat p (a m x)) → ∀ m, 0 ≤ padicValRat p (a' m x))
    (u : M) (hu : ∀ m, 0 ≤ padicValRat p (a m u))
    (hprim : ∃ m, a' m u ≠ 0 ∧ padicValRat p (a' m u) = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ M) (e : Fin n → ℕ) (i₀ : Fin n), b i₀ = u ∧ e i₀ = 0 ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a m (∑ i, c i • b i))) ↔ ∀ i, 0 ≤ padicValRat p (c i)) ∧
      (∀ c : Fin n → ℚ, (∀ m, 0 ≤ padicValRat p (a' m (∑ i, c i • b i))) ↔
        ∀ i, -(e i : ℤ) ≤ padicValRat p (c i)) := by sorry
