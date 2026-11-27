-- Prove2me | Theorems.Thm_OeisA158110_coeff_two_logSeries
-- name    : OeisA158110.coeff_two_logSeries
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-27T05:08:58.361584+00:00
-- url     : https://prove2.me/theorems/cb580ad1-ee6c-458c-982e-14cbfaeae236
-- title:
--   A158110 auxiliary series: coefficient of $x^2$
-- statement:
--   Let $L = \sum_{n \ge 1} 2^{n^3} x^n / n$ over $\mathbb{Q}$. The coefficient of $x^2$ in $L$ is $128$:
--
--   $$[x^2] L = \frac{2^{2^3}}{2} = \frac{256}{2} = 128.$$
--
--   The exponent is $2^3 = 8$, so the numerator is $2^8 = 256$. This is the dominant term of the second coefficient of $\exp(L)$.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib
import Definitions.Def_OeisA158110_Series
open PowerSeries

namespace OeisA158110

theorem coeff_two_logSeries : coeff 2 (logSeries 2 3) = 128 := by sorry

end OeisA158110
