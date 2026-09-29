-- Prove2me | Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul
-- name    : IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/1d882e2a-b50b-58f4-8c72-c5a118367951
-- title:
--   Rational function regular along a prime divisor and integral lies in R
-- statement:
--   Let $R$ be an integrally closed commutative domain and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$. Let $t \in R$ be nonzero and such that the principal ideal $\mathrm{span}\{t\}$ is prime. Let $f \in K$ and assume two conditions: first, that $f$ can be written with denominator prime to $t$, i.e. there exist $r, s \in R$ with $s \notin \mathrm{span}\{t\}$ and $f \cdot \iota(s) = \iota(r)$, where $\iota \colon R \to K$ is the structure map; second, that $f$ becomes integral after clearing a power of $t$, i.e. there exists $n \in \mathbb{N}$ such that $\iota(t)^n \cdot f$ is integral over $R$. The conclusion is that $f$ lies in the image of $\iota$: there exists $r \in R$ with $\iota(r) = f$.
--
--   This is the algebraic form of the statement that a rational function on a normal integral scheme which is regular at the generic point of a prime principal divisor $V(t)$ and integral over $R[1/t]$ is in fact regular, proved here with no Noetherian or finiteness hypotheses. It serves the local study of modular curves at nodes and at specialisations of places, being cited by [`ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral`](thm.html#ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral) and by the two prolongation-tuple lemmas [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_evalBar_eq_mul_evalBar_of_mem_integersSnd_of_isIntegral`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_evalBar_eq_mul_evalBar_of_mem_integersSnd_of_isIntegral) and `…_of_mem_integers_of_isIntegral`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow_mul
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht0 : t ≠ 0) (ht : (Ideal.span {t}).IsPrime)
    (f : K) (hv : ∃ r s : R, s ∉ Ideal.span {t} ∧ f * algebraMap R K s = algebraMap R K r)
    (hint : ∃ n : ℕ, IsIntegral R (algebraMap R K t ^ n * f)) :
    ∃ r : R, algebraMap R K r = f := by sorry
