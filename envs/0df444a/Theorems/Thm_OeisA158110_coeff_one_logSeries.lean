-- Prove2me | Theorems.Thm_OeisA158110_coeff_one_logSeries
-- name    : OeisA158110.coeff_one_logSeries
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-27T05:04:57.869935+00:00
-- url     : https://prove2.me/theorems/c153ace3-fb88-472d-abc4-a04472d1fa76
-- title:
--   A158110 auxiliary series: coefficient of $x$
-- statement:
--   Let $L = \sum_{n \ge 1} 2^{n^3} x^n / n$ over $\mathbb{Q}$. The coefficient of $x$ in $L$ is $2$:
--
--   $$[x^1] L = \frac{2^{1^3}}{1} = 2.$$
--
--   This value feeds the exponential coefficient identity at degree $2$, where it enters squared and halved.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib
import Definitions.Def_OeisA158110_Series
open PowerSeries

namespace OeisA158110

theorem coeff_one_logSeries : coeff 1 (logSeries 2 3) = 2 := by sorry

end OeisA158110
