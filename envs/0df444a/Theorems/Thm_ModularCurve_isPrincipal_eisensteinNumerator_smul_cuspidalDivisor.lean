-- Prove2me | Theorems.Thm_ModularCurve_isPrincipal_eisensteinNumerator_smul_cuspidalDivisor
-- name    : ModularCurve.isPrincipal_eisensteinNumerator_smul_cuspidalDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/b3675dad-df84-57a3-84c8-dcd9d715f69c
-- title:
--   Principality of n·((̄ 0)-(∞̄)) on X₀(ℓ)
-- statement:
--   Let $\ell$ be a prime. Write $F_\ell$ for [`ModularCurve.modularFunctionFieldBar ℓ`](def/ModularCurve_ArithmeticGalois.html#L111), the base change to $\overline{\mathbb Q}$ of the full modular function field of level $\ell$, realised as an intermediate field of the Laurent series field $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$. Divisors are the finitely supported $\mathbb Z$-valued functions on the set of places of $F_\ell$ over $\overline{\mathbb Q}$, a place being a valuation subring of $F_\ell$ which contains the image of $\overline{\mathbb Q}$, is not the whole field, and is a principal ideal ring. The cuspidal divisor [`ModularCurve.cuspidalDivisor ℓ`](def/ModularCurve_CuspidalClass.html#L28) is $(\bar 0)-(\bar\infty)$, that is, the difference of the indicator functions of the place `cuspZeroBar ℓ`, the translate of `cuspInftyBar ℓ` by the Fricke involution, and of the place `cuspInftyBar ℓ` attached via `qInftyPlaceBar` to the $q$-expansion of $j$. The assertion is that the integer multiple of this divisor by [`ModularCurve.eisensteinNumerator ℓ`](def/ModularCurve_ModularUnit.html#L169) $=(\ell-1)/\gcd(\ell-1,12)$ is principal: there exists a nonzero $f \in F_\ell$ such that for every place $v$ the value of that divisor at $v$ equals $v.\mathrm{ord}\, f$.
--
--   This is the classical statement that the cuspidal divisor $(\bar 0)-(\bar\infty)$ on $X_0(\ell)$ has order dividing the numerator $n$ of $(\ell-1)/12$, exhibited by an eta-quotient modular unit. It is the input to [`ModularCurve.addOrderOf_cuspidalClass_eq_eisensteinNumerator`](thm.html#ModularCurve.addOrderOf_cuspidalClass_eq_eisensteinNumerator), which determines the order of the cuspidal class in the divisor class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isPrincipal_eisensteinNumerator_smul_cuspidalDivisor.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.isPrincipal_eisensteinNumerator_smul_cuspidalDivisor (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : AlgebraicCurve.Divisor.IsPrincipal ((ModularCurve.eisensteinNumerator ℓ : ℤ) • ModularCurve.cuspidalDivisor ℓ) := by sorry
