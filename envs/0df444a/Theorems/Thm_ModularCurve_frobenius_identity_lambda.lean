-- Prove2me | Theorems.Thm_ModularCurve_frobenius_identity_lambda
-- name    : ModularCurve.frobenius_identity_lambda
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/0a6e957b-dce7-50d5-bd6c-5490fcd00340
-- title:
--   Frobenius identity for the λ-series in characteristic ℓ
-- statement:
--   Let $K$ be a commutative ring and $\ell$ a prime such that $K$ has characteristic $\ell$. Consider the integral Laurent series `lambdaInt` over $\mathbb{Z}$, namely the product of the monomial $q^{1}$, the eighth power of the power series `etaProd`, the series obtained from the sixteenth power of `etaProd` by the substitution $q \mapsto q^{4}$, and the series obtained from `dedekindEtaUnitInv` by $q \mapsto q^{2}$; here substitution $q \mapsto q^{N}$ means the exponent-rescaling ring endomorphism `qExpand`, induced on Hahn series by multiplication by $N$ on the exponent group $\mathbb{Z}$. Write `lambdaModC K` for the Laurent series over $K$ obtained by pushing the coefficients of `lambdaInt` forward along the canonical ring map $\mathbb{Z} \to K$. The assertion is the equality, in the Laurent series ring over $K$,
--   $$\mathrm{qExpand}_{K,\ell}(\overline{\lambda}) = \overline{\lambda}^{\,\ell},$$
--   where $\overline{\lambda} =$ `lambdaModC K`; that is, substituting $q^{\ell}$ for $q$ in the reduction of the $\lambda$-series agrees with raising that reduction to the $\ell$-th power.
--
--   This is the Frobenius (freshman's dream) identity for the level-two modular function series in characteristic $\ell$: a Laurent series with coefficients in the image of $\mathbb{Z}$ satisfies $f(q)^{\ell} = f(q^{\ell})$. It is used in the Kronecker-type congruence for the $\lambda$-series, [`ModularCurve.kroneckerCongruence_lambda`](thm.html#ModularCurve.kroneckerCongruence_lambda), and in [`ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero`](thm.html#ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobenius_identity_lambda.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.frobenius_identity_lambda (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    lambdaNModC K ℓ = (lambdaModC K) ^ ℓ := by sorry
