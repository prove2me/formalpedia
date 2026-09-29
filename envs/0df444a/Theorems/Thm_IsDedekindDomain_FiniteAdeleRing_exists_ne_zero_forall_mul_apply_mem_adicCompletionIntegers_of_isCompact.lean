-- Prove2me | Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
-- name    : IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/06e8bb34-1d7c-5243-91c7-cf0e0a8bd269
-- title:
--   A common denominator for a compact set of finite adeles
-- statement:
--   Let $R$ be a Dedekind domain and $K$ a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $C$ be a subset of the finite adele ring `IsDedekindDomain.FiniteAdeleRing R K` (the restricted product of the completions $K_v$ over the height-one primes $v$ of $R$ with respect to the rings of integers $\mathcal{O}_v$) which is compact for the adelic topology. Then there exists $s \in R$ with $s \neq 0$ such that for every $y \in C$ and every $v$ in the height-one spectrum of $R$, the $v$-component of the product of the image of $s$ under the structure map $R \to \mathbb{A}_{K,f}$ with $y$ lies in `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v`, i.e. $(sy)_v \in \mathcal{O}_v$. Thus a single nonzero element of $R$ clears denominators simultaneously at all finite places for all members of $C$. No bound on $s$ is asserted, and the statement is an existence assertion only.
--
--   This is the standard statement that a compact set of finite adeles admits one common denominator, so that $C \subseteq s^{-1}\prod_v \mathcal{O}_v$ for a single nonzero $s \in R$. It is used in the analytic parts of the argument where sums or integrals over a compact set of adelic data must be compared with a lattice or a fractional ideal, for instance in the estimates for Whittaker coefficients and for Riemann-sum approximations of unipotent integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact.lean

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Set (IsDedekindDomain.FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ C, ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      (algebraMap R (IsDedekindDomain.FiniteAdeleRing R K) s * y) v
        ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v := by sorry
