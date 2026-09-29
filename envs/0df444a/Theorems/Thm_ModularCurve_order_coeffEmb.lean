-- Prove2me | Theorems.Thm_ModularCurve_order_coeffEmb
-- name    : ModularCurve.order_coeffEmb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/b59606ce-9f0c-522b-a285-96a1a61dafa6
-- title:
--   Coefficientwise base change preserves the order of a Laurent series
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $x$ be a formal Laurent series with rational coefficients, i.e. an element of `LaurentSeries ℚ`, the Hahn series ring over $\mathbb{Q}$ with value group $\mathbb{Z}$. Write `coeffEmb L` for the ring homomorphism `LaurentSeries ℚ →+* LaurentSeries L` obtained from `coeffMap` applied to the structure map $\mathbb{Q} \to L$, that is, the map sending a series to the series whose coefficient at each exponent is the image of the corresponding coefficient of $x$ under $\mathbb{Q} \to L$ (this is a ring homomorphism: it preserves $0$, $1$, sums and products). The assertion is the equality of orders $$\operatorname{order}(\mathrm{coeffEmb}_L(x)) = \operatorname{order}(x),$$ where the order of a Hahn series is its least exponent carrying a nonzero coefficient, with the convention that the zero series has order $0$. No hypothesis beyond $L$ being a field that is a $\mathbb{Q}$-algebra is imposed; in particular $L$ may be of arbitrary transcendence degree, and $x$ may be zero.
--
--   This records that base change of coefficients along a field extension of $\mathbb{Q}$ is order-preserving on $q$-expansions, so that vanishing orders at the cusp computed over $\mathbb{Q}$ may be transported to $L$. It is used in the treatment of $q$-expansions of modular functions and modular units over a general coefficient field, for instance in the computations of orders of $j(q)$ and of modular unit series and in the divisibility statement for the order of a cuspidal divisor class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_order_coeffEmb.lean

import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.order_coeffEmb (L : Type*) [Field L] [Algebra ℚ L] (x : LaurentSeries ℚ) : (coeffEmb L x).order = x.order := by sorry
