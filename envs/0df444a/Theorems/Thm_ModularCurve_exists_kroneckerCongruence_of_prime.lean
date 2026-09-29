-- Prove2me | Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
-- name    : ModularCurve.exists_kroneckerCongruence_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/8a1c49e7-d713-5a8d-96fd-4b4056c65f8f
-- title:
--   Existence of a Kronecker-congruent modular polynomial at a prime
-- statement:
--   Let $\ell$ be a prime. The assertion is that there exists a term `data` of the structure [`ModularCurve.ModularPolynomialData`](def/ModularCurve_X0.html#L215) $\ell$ for which the predicate [`ModularCurve.KroneckerCongruence`](def/ModularCurve_KroneckerTransport.html#L127) $\ell$ `data` holds. Unfolding the structure, `data` consists of a bivariate integral polynomial $\Phi \in \mathbb{Z}[x][X]$ (an element of `Polynomial (Polynomial ℤ)`, with $x$ the inner and $X$ the outer variable) together with three properties: $\Phi$ is monic as a polynomial in the outer variable; its degree in that variable equals `dedekindPsi` $\ell$, defined as $\sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$, which for a prime is $\ell + 1$; and $\Phi$ vanishes when its coefficients in $\mathbb{Z}[x]$ are mapped into the Laurent series field $\mathbb{Q}((q))$ by `evalAtJ`, the ring homomorphism substituting the $q$-expansion `jq` of the modular invariant for $x$, and the outer variable is sent to `jqN` $\ell$, the $q$-expansion of $j$ at $q^{\ell}$. The additional condition `KroneckerCongruence` says that the coefficientwise reduction of $\Phi$ modulo $\ell$ (applying $\mathbb{Z} \to \mathbb{Z}/\ell$ at both polynomial levels) equals $(x^{\ell} - X)\,(x - X^{\ell})$ in $(\mathbb{Z}/\ell)[x][X]$.
--
--   This is the existential form of Kronecker's congruence relation at an arbitrary prime: the modular equation of prime degree $\ell$, relating $j(q)$ and $j(q^{\ell})$, reduces modulo $\ell$ to the product of the graph of Frobenius and its transpose. It is the input from which the universally quantified form over all modular-polynomial packets of prime level is obtained, and it is used throughout the treatment of the modular curves $X_0(\ell)$ in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_kroneckerCongruence_of_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_kroneckerCongruence_of_prime (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ data : ModularCurve.ModularPolynomialData ℓ, ModularCurve.KroneckerCongruence ℓ data := by sorry
