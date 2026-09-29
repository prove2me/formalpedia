-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic
-- name    : GaloisRepAdic.exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d2f73e6b-0e1d-543e-b1e2-e1a41bd5d587
-- title:
--   Nontriviality on inertia above p for cyclotomic determinant
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be a [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is: a free finite $A$-module $V$ with $\operatorname{rank}_A V = 2$, together with a monoid homomorphism $\rho.\rho \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \operatorname{End}_A V$ (for the fixed model $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`) which is adically continuous in the sense that for every $n$ there is a finite subextension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_A^n \cdot V$ for all $v \in V$. Let $p$ be a prime with $(p : A) \neq 0$, and assume `ρ.DetIsCyclotomic p`, i.e. $(p:A)$ lies in the maximal ideal of $A$ and, for all $n \in \mathbb{N}$, all $\sigma$ and all $a \in \mathbb{N}$, if $\sigma\mu = \mu^a$ for every $\mu \in \overline{\mathbb{Q}}$ with $\mu^{p^n} = 1$, then $\det(\rho(\sigma)) - a \in (p^n)A$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, meaning that $p$ is a nonunit of $P$. Then there exists $\sigma$ in the image of the inertia subgroup of $P$ inside the decomposition subgroup, viewed as a subgroup of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, with $\rho.\rho\,\sigma \neq 1$.
--
--   This records the ramifiedness at $p$ of a two-dimensional representation whose determinant is the cyclotomic character: such a representation cannot be unramified at any place above $p$ once $p \neq 0$ in the coefficient ring. It is used in the local analysis of ordinarity at $p$, feeding the statements about unit roots and ordinary points of the Hecke-local setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic.lean

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime)
    (hp0 : (p : A) ≠ 0) (hdet : ρ.DetIsCyclotomic p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ ≠ 1 := by sorry
