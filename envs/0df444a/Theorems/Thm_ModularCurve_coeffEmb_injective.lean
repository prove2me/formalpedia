-- Prove2me | Theorems.Thm_ModularCurve_coeffEmb_injective
-- name    : ModularCurve.coeffEmb_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/f6fc8541-669e-5884-8b15-9534e19b03e3
-- title:
--   Injectivity of the coefficient embedding ℚ((q)) → L((q))
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure. For a ring homomorphism $f \colon R \to S$ of commutative rings, [`ModularCurve.coeffMap f`](def/ModularCurve_LaurentCoeff.html#L16) denotes the ring homomorphism $\mathrm{LaurentSeries}\,R \to \mathrm{LaurentSeries}\,S$ obtained by applying $f$ to each coefficient, that is, sending a formal Laurent series (a Hahn series over $\mathbb{Z}$) $\sum_k a_k q^k$ to $\sum_k f(a_k) q^k$; and [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) is the instance of this construction for the structure map $\mathbb{Q} \to L$, a ring homomorphism $\mathbb{Q}((q)) \to L((q))$. The theorem asserts that this map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) is injective as a function.
--
--   An elementary compatibility statement about the coefficientwise extension of scalars on formal Laurent series, recording that $q$-expansions with rational coefficients are determined by their images over any field of characteristic zero containing $\mathbb{Q}$. It is used throughout the treatment of $q$-expansions on modular curves, for instance in the descent arguments for generators of the function field (pole orders, values of coefficients, and behaviour at the cusp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffEmb_injective.lean

import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.coeffEmb_injective (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (ModularCurve.coeffEmb L) := by sorry
