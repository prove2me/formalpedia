-- Prove2me | Theorems.Thm_ModularCurve_qExpand_two_etaProd_pow_twentyfour
-- name    : ModularCurve.qExpand_two_etaProd_pow_twentyfour
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/090d3b78-6a7a-5163-827d-0997aa41085d
-- title:
--   Jacobi's quartic identity as an eta-product identity
-- statement:
--   The statement is a closed identity in the ring $\mathbb{Z}((q))$ of integer Laurent series (formal Hahn series over $\mathbb{Z}$ with value group $\mathbb{Z}$). Write $P =$ `etaProd` for the Euler product $\prod_{n \ge 1}(1 - X^{n})$ in $\mathbb{Z}[[X]]$, regarded inside $\mathbb{Z}((q))$ via `HahnSeries.ofPowerSeries`, and for $N \ge 1$ let `qExpand ℤ N` be the ring endomorphism of $\mathbb{Z}((q))$ obtained by pushing a Laurent series forward along the (strictly monotone, injective) multiplication-by-$N$ map on the exponent group $\mathbb{Z}$, that is the substitution $q \mapsto q^{N}$. Finally `HahnSeries.single (1 : ℤ) (1 : ℤ)` is the monomial $q$. The asserted equality is $$P(q^{2})^{24} = P(q)^{16}\,P(q^{4})^{8} + 16\,q\,P(q)^{8}\,P(q^{4})^{16},$$ with the first summand on the right formed as $P(q)^{16}$ times the image of $P^{8}$ under $q \mapsto q^{4}$, and the second as $16\,q$ times $P(q)^{8}$ times the image of $P^{16}$ under $q \mapsto q^{4}$. There are no variables or hypotheses.
--
--   This is Jacobi's quartic theta identity $\vartheta_3^4 = \vartheta_2^4 + \vartheta_4^4$ written purely in terms of Euler products: with $q = e^{\pi i \tau}$ it is the Dedekind eta relation $\eta(\tau)^{24} = \eta(\tau/2)^{16}\eta(2\tau)^{8} + 16\,\eta(\tau/2)^{8}\eta(2\tau)^{16}$, equivalently $1 = (1-\lambda) + \lambda$ for the modular lambda function. It is used in the computations of the $q$-expansions of $\lambda$ and of $j$ in [`ModularCurve.qExpand_two_jq_mul_lambdaModC_sq`](thm.html#ModularCurve.qExpand_two_jq_mul_lambdaModC_sq), [`ModularCurve.jq_mul_lambdaModC_mul_one_sub_pow_four`](thm.html#ModularCurve.jq_mul_lambdaModC_mul_one_sub_pow_four) and [`ModularCurve.qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four`](thm.html#ModularCurve.qExpand_four_jq_mul_one_sub_mul_lambdaModC_pow_four).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_two_etaProd_pow_twentyfour.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.qExpand_two_etaProd_pow_twentyfour :
    qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) =
      HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16 * qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8) +
        16 * HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 *
          qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) := by sorry
