-- Prove2me | Theorems.Thm_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg
-- name    : ModularCurve.minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/a215d33a-7b97-55dd-bf3c-16deeac8563a
-- title:
--   Integrality of the minimal polynomial of λ(q^q) over ℚ(λ)
-- statement:
--   Fix a natural number $q$ carrying a primality instance and assume $q \neq 2$, so that $q$ is an odd prime. Work inside the field $\mathbb Q((\mathfrak q))$ of Laurent series over $\mathbb Q$ (Hahn series with integer exponents), and write $\lambda =$ `lambdaModC ℚ` for the series obtained from the explicit integral series `lambdaInt` — the product of $\mathfrak q$, the eighth power of the eta product, its sixteenth power with exponents doubled by the substitution $\mathfrak q \mapsto \mathfrak q^{4}$, and the inverse eta unit with exponents doubled by $\mathfrak q \mapsto \mathfrak q^{2}$ — by applying the coefficientwise ring map $\mathbb Z \to \mathbb Q$. Let $K = \mathbb Q(\lambda)$ be the intermediate field of $\mathbb Q((\mathfrak q))$ generated over $\mathbb Q$ by $\lambda$, and let `lambdaNModC ℚ q` be the series obtained from $\lambda$ by the exponent-scaling ring homomorphism `qExpand ℚ q`, i.e. by the substitution $\mathfrak q \mapsto \mathfrak q^{q}$. The assertion is that for every natural number $k$ and every integer $n < 0$, the coefficient at exponent $n$ of the $k$-th coefficient of the minimal polynomial of `lambdaNModC ℚ q` over $K$, viewed as an element of $\mathbb Q((\mathfrak q))$ through the inclusion $K \subseteq \mathbb Q((\mathfrak q))$, vanishes. Equivalently, every coefficient of that minimal polynomial lies in $\mathbb Q[[\mathfrak q]]$.
--
--   This is the integrality half of the modular equation of level $q$ for the normalised Legendre series $\lambda$, the analogue for $\Gamma_0(4) \cap \Gamma_0(q)$ of Kronecker's classical statement that the modular polynomial relating $j(\mathfrak q)$ and $j(\mathfrak q^q)$ has $\mathfrak q$-integral (indeed integral) coefficients. It feeds into [`ModularCurve.minpoly_lambdaNModC_coeff_mem_adjoin`](thm.html#ModularCurve.minpoly_lambdaNModC_coeff_mem_adjoin), which upgrades the conclusion to membership of the coefficients in a prescribed ring of coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (k : ℕ) (n : ℤ) (hn : n < 0) :
    (((minpoly (↥(IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)))) (lambdaNModC ℚ q)).coeff k
        : LaurentSeries ℚ)).coeff n = 0 := by sorry
