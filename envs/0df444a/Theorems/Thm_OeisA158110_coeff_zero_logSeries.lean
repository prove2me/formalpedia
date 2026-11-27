-- Prove2me | Theorems.Thm_OeisA158110_coeff_zero_logSeries
-- name    : OeisA158110.coeff_zero_logSeries
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-27T05:01:09.288737+00:00
-- url     : https://prove2.me/theorems/9781110c-47bb-4a95-844b-f3f92d5c22ee
-- title:
--   A158110 auxiliary series: constant coefficient
-- statement:
--   Let $L = \sum_{n \ge 1} 2^{n^3} x^n / n$ over $\mathbb{Q}$. The constant coefficient of $L$ is $0$:
--
--   $$[x^0] L = 0.$$
--
--   This is the first coefficient computation for the auxiliary series; later coefficient identities for $\exp(L)$ use it to remove the cross terms in the square $L^2$.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib
import Definitions.Def_OeisA158110_Series
open PowerSeries

namespace OeisA158110

theorem coeff_zero_logSeries : coeff 0 (logSeries 2 3) = 0 := by sorry

end OeisA158110
