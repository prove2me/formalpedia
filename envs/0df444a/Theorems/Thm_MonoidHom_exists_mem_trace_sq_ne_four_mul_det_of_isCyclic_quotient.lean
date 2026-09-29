-- Prove2me | Theorems.Thm_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient
-- name    : MonoidHom.exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/ed8cfb57-13c4-5677-815f-0a729be6f6f3
-- title:
--   Absolutely irreducible 2-dimensional ρ is regular semisimple on N
-- statement:
--   Let $G$ be a group and $\mathbb{k}$ a field in which $2 \neq 0$, and let $\rho \colon G \to M_2(\mathbb{k})$ be a multiplicative map, i.e. a monoid homomorphism from $G$ into the multiplicative monoid of $2 \times 2$ matrices over $\mathbb{k}$ (no invertibility of the values is assumed as a hypothesis). Assume that $\rho$ is absolutely irreducible in Burnside's form: the $\mathbb{k}$-subspace of $M_2(\mathbb{k})$ spanned by the set of values $\{\rho(g) : g \in G\}$ is all of $M_2(\mathbb{k})$. Let $N$ be a normal subgroup of $G$ whose quotient $G/N$ is cyclic. The conclusion is that there exists $\sigma \in N$ with $$\operatorname{tr}(\rho\sigma)^2 \neq 4\det(\rho\sigma),$$ that is, an element of $N$ whose image has nonvanishing characteristic-polynomial discriminant, so that over an algebraic closure of $\mathbb{k}$ it has two distinct eigenvalues and is in particular regular semisimple. Only the existence of one such $\sigma$ is asserted; no information about its location in $N$ or about the eigenvalues themselves is given.
--
--   This is the group-theoretic ingredient in the construction of Taylor–Wiles primes: applied to the Galois group of a finite extension cut out by a residual representation and to the normal subgroup fixing the $p^n$-th roots of unity, it supplies an element acting trivially on $\mu_{p^n}$ whose image has distinct eigenvalues, whence by a density argument primes $q \equiv 1 \bmod p^n$ with regular semisimple Frobenius image. It is used here in [`TaylorWiles.exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues`](thm.html#TaylorWiles.exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MonoidHom.exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient
    {G : Type*} [Group G] {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) 𝕜)
    (hρ : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] :
    ∃ σ ∈ N, (ρ σ).trace ^ 2 ≠ 4 * (ρ σ).det := by sorry
