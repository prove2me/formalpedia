-- Prove2me | Theorems.Thm_OeisA158110_coeff_two_logSeries_sq
-- name    : OeisA158110.coeff_two_logSeries_sq
-- status  : Open
-- author  : @pageman
-- created : 2026-11-27T05:14:06.523162+00:00
-- url     : https://prove2.me/theorems/521a1229-e3bf-5d09-b394-24e70e32ee96
-- title:
--   A158110 auxiliary series: coefficient of $x^2$ in $L^2$
-- statement:
--   Let $L = \sum_{n \ge 1} 2^{n^3} x^n / n$ over $\mathbb{Q}$. The coefficient of $x^2$ in the square $L^2$ equals the square of the coefficient of $x$ in $L$:
--
--   $$[x^2] L^2 = \left([x^1] L\right)^2.$$
--
--   The convolution for degree $2$ has three terms; the two terms that involve the constant coefficient of $L$ vanish because that coefficient is $0$, and the middle term is the square displayed above.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib
import Definitions.Def_OeisA158110_Series
open PowerSeries

namespace OeisA158110

theorem coeff_two_logSeries_sq :
    coeff 2 ((logSeries 2 3) ^ 2) = (coeff 1 (logSeries 2 3)) ^ 2 := by sorry

end OeisA158110
