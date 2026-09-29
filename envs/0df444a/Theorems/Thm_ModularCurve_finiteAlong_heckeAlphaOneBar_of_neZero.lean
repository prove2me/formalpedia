-- Prove2me | Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaOneBar_of_neZero
-- name    : ModularCurve.finiteAlong_heckeAlphaOneBar_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/eaa0ea97-8c9a-5e4d-b5cd-bd0d15a8536e
-- title:
--   Finiteness of the first degeneracy extension along α₁
-- statement:
--   Let $L$ be a field equipped with an algebra structure over $\mathbb{Q}$, and let $N$ and $\ell$ be non-zero natural numbers. Inside the Laurent series field $L(\!(q)\!)$ consider the two intermediate fields obtained by base change from $\mathbb{Q}$: namely $\mathrm{laurentBaseChange}\ L$ applied to the $q$-expansion function field of $X_1(N)$ over $\mathbb{Q}$, i.e. the subfield of $L(\!(q)\!)$ generated over $L$ by the image of $\mathbb{Q}$-rational $q$-expansions under the coefficientwise embedding $L(\!(q)\!)\supseteq\mathbb{Q}(\!(q)\!)$, and likewise $\mathrm{laurentBaseChange}\ L$ applied to the $q$-expansion function field over $\mathbb{Q}$ of the congruence subgroup $\Gamma_1(N)\cap\Gamma_0(N\ell)$. Since the first of these $\mathbb{Q}$-function fields is contained in the second, the base changes are nested, and [`ModularCurve.heckeAlphaOneBar L N ℓ`](def/ModularCurve_X1HeckeOperator.html#L66) is the resulting inclusion, viewed as an $L$-algebra homomorphism. The assertion is [`AlgebraicCurve.FiniteAlong`](def/AlgebraicCurve_Correspondence.html#L37) for this map: when the larger field $L\cdot F(\Gamma_1(N)\cap\Gamma_0(N\ell))$ is regarded as a module over the smaller field $L\cdot F(\Gamma_1(N))$ through that inclusion, it is a finite module. No primality or coprimality assumption is imposed on $\ell$ or on $N$ beyond both being non-zero.
--
--   This is the function-field form of the statement that the forgetful degeneracy map $X(\Gamma_1(N)\cap\Gamma_0(N\ell))\to X_1(N)$ is a finite morphism of curves, here for arbitrary $\ell\ge 1$ rather than only for primes. It underlies the divisor-theoretic treatment of the first degeneracy pull-back, and is used in the construction of supports of Hecke divisors twisted by diamond and Atkin–Lehner operators and in the production of degeneracy pairs on two-chart models of $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteAlong_heckeAlphaOneBar_of_neZero.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finiteAlong_heckeAlphaOneBar_of_neZero (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] :
    AlgebraicCurve.FiniteAlong L (ModularCurve.heckeAlphaOneBar L N ℓ) := by sorry
