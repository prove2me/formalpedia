-- Prove2me | Theorems.Thm_ModularCurve_delta_pow_mul_deuringPolynomial_lambda_pow_twelve
-- name    : ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/74e79339-2239-575a-a516-bb03e248043f
-- title:
--   Level-two Deuring polynomial identity in characteristic q
-- statement:
--   Let $q$ be a prime with $q \ge 5$ and let $k$ be a field of characteristic $q$. All terms live in the ring `LaurentSeries k` of Hahn series over $k$ indexed by $\mathbb{Z}$. Write $\Delta$ for the image in `LaurentSeries k` of the power series $X \cdot$ `dedekindEtaUnit` $= X\prod_{n\ge 1}(1-X^{n})^{24}$ with coefficients reduced into $k$, and let `qExpand k 2` be the ring homomorphism doubling all exponents, so that the first factor is $\Delta$ evaluated at the square of the variable. Write $\mu =$ `lambdaModC k` for the coefficientwise reduction to $k$ of $$\mathrm{lambdaInt} = X\cdot\Big(\prod_{n\ge1}(1-X^{n})\Big)^{8}\cdot\Big(\prod_{n\ge1}(1-X^{4n})\Big)^{16}\cdot \mathrm{dedekindEtaUnitInv}(X^{2}),$$ the last factor being the series `dedekindEtaUnitInv` with exponents doubled. Let $H_q(X)=\sum_{i=0}^{(q-1)/2}\binom{(q-1)/2}{i}^{2}X^{i}$ be `deuringPolynomial q`, reduced mod $q$ and evaluated at $16\mu$. The assertion is the identity $$\big(\Delta(X^{2})\big)^{q-1}\cdot H_q(16\mu)^{12} = \big(\mu\,(1-16\mu)\big)^{2(q-1)}$$ in `LaurentSeries k`, the exponents being natural-number subtractions.
--
--   This is the level-two form of the congruence $E_{q-1}\equiv 1 \pmod q$: it compares the Hasse invariant of the Legendre curve with parameter $16\mu$, which is a multiple of the Deuring polynomial $H_q$, with that of the Tate curve of parameter $X^{2}$, using that $\mathrm{Hasse}^{12}/\Delta^{q-1}$ depends only on the $j$-invariant. It is used by [`ModularCurve.deuringPolynomial_sq_mul_thetaL_lambda_pow`](thm.html#ModularCurve.deuringPolynomial_sq_mul_thetaL_lambda_pow) in the study of supersingular parameters in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_delta_pow_mul_deuringPolynomial_lambda_pow_twelve.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    qExpand k 2 (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))) ^ (q - 1)
        * (Polynomial.aeval (16 * lambdaModC k) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k))) ^ 12
      = (lambdaModC k * (1 - 16 * lambdaModC k)) ^ (2 * (q - 1)) := by sorry
