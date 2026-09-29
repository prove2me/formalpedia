-- Prove2me | Theorems.Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic
-- name    : LaurentSeries.eq_C_coeff_zero_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/bc815168-6956-512b-bb9b-a1b91668f435
-- title:
--   K is algebraically closed in K((X))
-- statement:
--   Let $K$ be a field and let $x$ be a formal Laurent series over $K$, i.e. an element of `LaurentSeries K`, the Hahn series with integer exponents and coefficients in $K$ whose support is well-ordered. Assume that $x$ is algebraic over $K$ in the sense of `IsAlgebraic K x`: there is a nonzero polynomial $p \in K[X]$ with $p(x) = 0$, the evaluation being taken along the algebra structure of `LaurentSeries K` over $K$. The conclusion is that $x$ coincides with the constant Laurent series `HahnSeries.C (x.coeff 0)`, namely the series whose coefficient in degree $0$ equals the degree-$0$ coefficient of $x$ and whose coefficients in all other degrees vanish. Equivalently, an element of $K((X))$ algebraic over $K$ lies in the image of $K$ and is determined by its constant term, so $K$ is algebraically closed in $K((X))$.
--
--   This is the standard statement that a field is algebraically closed inside its field of formal Laurent series; in the geometric language, the constants of the local field $K((X))$ are $K$ itself. It is used in the formalisation when identifying algebraic, or integral, elements of $q$-expansion rings with constants, for instance in the treatment of charts and connectedness for models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LaurentSeries.eq_C_coeff_zero_of_isAlgebraic {K : Type*} [Field K] {x : LaurentSeries K} (hx : IsAlgebraic K x) : x = HahnSeries.C (x.coeff 0) := by sorry
