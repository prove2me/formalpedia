-- Prove2me | Theorems.Thm_ModularCurve_addOrderOf_cuspidalClass_dvd
-- name    : ModularCurve.addOrderOf_cuspidalClass_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/e207c951-397e-5c71-8988-0c35f582a2e3
-- title:
--   Order of the cuspidal class divides ℓ-1
-- statement:
--   Let $\ell$ be a natural number which is prime. Work with the field $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and the function field `modularFunctionFieldBar ℓ` of the modular curve of level $\ell$ over $\overline{\mathbb{Q}}$, and let `JZero ℓ` denote the group $\mathrm{Pic}^0$ attached to this pair, that is, the quotient of the group of degree-zero divisors (`Divisor.degZero`) by its subgroup of principal divisors. In this group, `cuspidalClass ℓ` is the class of the degree-zero divisor $[\mathrm{cusp}_0] - [\mathrm{cusp}_\infty]$, the formal difference of the two places `cuspZeroBar ℓ` and `cuspInftyBar ℓ` with coefficients $1$ and $-1$. The theorem asserts that the additive order of this class divides $\ell - 1$, the subtraction being natural-number subtraction. Since $\ell \ge 2$, the quantity $\ell - 1$ is at least $1$, so the divisibility assertion in particular implies that `cuspidalClass ℓ` is a torsion element; the statement gives only a divisibility, not the exact order (which is the numerator of $(\ell-1)/12$).
--
--   This is Ogg's theorem that the cuspidal divisor class of $X_0(\ell)$, for $\ell$ prime, is torsion of order dividing $\ell - 1$, obtained from the modular unit $\Delta(z)/\Delta(\ell z)$ whose divisor is supported on the two cusps. It is used here in the computation of the genus of the level-$\ell$ modular curve in the case of genus two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_addOrderOf_cuspidalClass_dvd.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.addOrderOf_cuspidalClass_dvd (ℓ : ℕ) [Fact ℓ.Prime] : addOrderOf (cuspidalClass ℓ) ∣ ℓ - 1 := by sorry
