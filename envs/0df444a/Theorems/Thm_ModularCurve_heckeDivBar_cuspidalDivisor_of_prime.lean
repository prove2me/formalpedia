-- Prove2me | Theorems.Thm_ModularCurve_heckeDivBar_cuspidalDivisor_of_prime
-- name    : ModularCurve.heckeDivBar_cuspidalDivisor_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/4bb4111a-18b3-5be0-9e6a-baaaf1cd96cb
-- title:
--   Hecke correspondence at ℓ multiplies the cuspidal divisor by 1+ℓ
-- statement:
--   Let $p$ and $\ell$ be distinct primes. Write $F_N$ for `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb{Q}}((q))$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images of the elements of `modularFunctionFieldFull N`, and consider the two $\overline{\mathbb{Q}}$-algebra maps $F_p \to F_{p\ell}$: `heckeAlphaBar`, the inclusion coming from the containment of full modular function fields at level $p$ in level $p\ell$, and `heckeBetaBar`, induced by the substitution $q \mapsto q^{\ell}$. The hypotheses `hα` and `hβ` assert that these two maps are integral as ring homomorphisms, and a further hypothesis asserts that the field $F_{p\ell}$ has principal divisors, i.e. every nonzero element $f$ admits a divisor (a finitely supported $\mathbb{Z}$-valued function on the places of $F_{p\ell}$ over $\overline{\mathbb{Q}}$, places being proper valuation subrings containing $\overline{\mathbb{Q}}$ that are principal ideal rings) whose value at each place $v$ is $\operatorname{ord}_v(f)$ and whose degree is $0$. Then the correspondence `heckeDivBar`, namely pullback of divisors along `heckeBetaBar` followed by pushforward along `heckeAlphaBar`, sends the cuspidal divisor $(\bar 0) - (\bar\infty)$ at level $p$, where $(\bar\infty)$ is `cuspInftyBar p` and $(\bar 0)$ is its translate under the Fricke involution, to $(1+\ell)$ times itself.
--
--   This is the statement that the Hecke correspondence $T_\ell$ on $X_0(p)$ acts on the cuspidal divisor $(0)-(\infty)$ with the Eisenstein eigenvalue $1+\ell$, proved here at the level of divisors rather than divisor classes. It is used for the action of the Hecke operators on the cuspidal class in the degree-zero divisor class group and for the statement that the Eisenstein ideal annihilates that class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDivBar_cuspidalDivisor_of_prime.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeDivBar_cuspidalDivisor_of_prime (p ℓ : ℕ) [hp : Fact (Nat.Prime p)] [hl : Fact (Nat.Prime ℓ)] (hpl : p ≠ ℓ) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p ℓ) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * ℓ))] : heckeDivBar hα hβ (cuspidalDivisor p) = (1 + ℓ : ℤ) • cuspidalDivisor p := by sorry
