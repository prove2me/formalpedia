-- Prove2me | Theorems.Thm_Matrix_hasDistinctRationalEigenvalues_pow
-- name    : Matrix.hasDistinctRationalEigenvalues_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/77698300-2d76-5603-943b-b1c0fccda74a
-- title:
--   Coprime powers preserve distinct rational eigenvalues
-- statement:
--   Let $\mathbb{k}$ be a field and $M$ a $2\times 2$ matrix over $\mathbb{k}$. Suppose $d$ is a natural number with $0 < d$ and $M^d = 1$, and suppose $M$ satisfies the predicate [`Matrix.HasDistinctRationalEigenvalues`](def/TaylorWiles_Primes.html#L31), that is: there are $\alpha,\beta \in \mathbb{k}$ with $\alpha \neq \beta$, $\operatorname{tr} M = \alpha + \beta$ and $\det M = \alpha\beta$ (so the characteristic polynomial of $M$ splits over $\mathbb{k}$ with two distinct roots; no semisimplicity or diagonalisability is asserted beyond this condition on the trace and determinant). Let $k$ be a natural number coprime to $d$, in the sense $\gcd(k,d) = 1$. The conclusion is that $M^k$ again satisfies [`Matrix.HasDistinctRationalEigenvalues`](def/TaylorWiles_Primes.html#L31): there exist two distinct elements of $\mathbb{k}$ whose sum is $\operatorname{tr}(M^k)$ and whose product is $\det(M^k)$. The witnesses produced are $\alpha^k$ and $\beta^k$ for the pair $(\alpha,\beta)$ given by the hypothesis on $M$.
--
--   This is the eigenvalue-ratio lemma: stability of split regular semisimplicity (in the trace-and-determinant formulation used in this development) under passage to a power coprime to the order of the matrix. It is used in the selection of Taylor–Wiles primes, via [`TaylorWiles.exists_isTaylorWilesPrime_of_statement`](thm.html#TaylorWiles.exists_isTaylorWilesPrime_of_statement), where a Frobenius element is pinned down only up to a coprime power of a chosen seed element and the distinct-eigenvalue clause must survive that ambiguity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_hasDistinctRationalEigenvalues_pow.lean

import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.hasDistinctRationalEigenvalues_pow {𝕜 : Type*} [Field 𝕜]
    {M : Matrix (Fin 2) (Fin 2) 𝕜} {d : ℕ} (hd : 0 < d) (hM : M ^ d = 1)
    (h : M.HasDistinctRationalEigenvalues) {k : ℕ} (hk : k.Coprime d) :
    (M ^ k).HasDistinctRationalEigenvalues := by sorry
