-- Prove2me | Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_modularPolynomialData
-- name    : ModularCurve.heckeAlphaBarIntegral_of_modularPolynomialData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/364a50ed-040c-5508-aa85-f5e1807dc81a
-- title:
--   Integrality of the α-leg from a modular polynomial
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a non-zero natural number, and suppose given `data : ModularCurve.ModularPolynomialData ℓ`, that is, a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic (in $Y$), whose degree equals $\psi(\ell) = \sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$, and which satisfies $\Phi = 0$ after evaluating its coefficients in $\mathbb{Z}[X]$ at the $q$-expansion $j(q)$ of the modular invariant, via `evalAtJ`, and its outer variable at the $q$-expansion `jqN ℓ` of $j(q^{\ell})$, both regarded in the Laurent series field $\mathbb{Q}((q))$. Assume in addition that $\ell$ is prime, and let $N$ be a non-zero natural number. The conclusion is [`ModularCurve.HeckeAlphaBarIntegral L N ℓ`](def/ModularCurve_HeckeOperator.html#L124): the ring homomorphism underlying the $L$-algebra map `heckeAlphaBar L N ℓ`, namely the inclusion of `laurentBaseChange L (modularFunctionFieldFull N)` into `laurentBaseChange L (modularFunctionFieldFull (N * ℓ))` coming from monotonicity of the base change along the divisibility $N \mid N\ell$, is integral, i.e. every element of the larger field is a root of a monic polynomial with coefficients in the image of the smaller one.
--
--   This is the integrality of the $\alpha$-leg (the degeneracy inclusion of the all-divisors modular function field of level $N$ into that of level $N\ell$), one of the named inputs required to construct the Hecke correspondence on the Jacobian side. It is used by [`ModularCurve.heckeAlphaBarIntegral_of_prime`](thm.html#ModularCurve.heckeAlphaBarIntegral_of_prime), where the modular polynomial datum for a prime $\ell$ is produced separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeAlphaBarIntegral_of_modularPolynomialData.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeAlphaBarIntegral_of_modularPolynomialData (L : Type*) [Field L] [Algebra ℚ L] {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] : ModularCurve.HeckeAlphaBarIntegral L N ℓ := by sorry
