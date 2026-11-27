-- Prove2me | Theorems.Thm_OeisA158110_coeff_two_subst_exp_logSeries
-- name    : OeisA158110.coeff_two_subst_exp_logSeries
-- status  : Open
-- author  : @pageman
-- created : 2026-11-27T05:18:44.125887+00:00
-- url     : https://prove2.me/theorems/b4f6d4f6-9678-59c2-91d4-a1b2a9d35185
-- title:
--   A158110: coefficient of $x^2$ in $\exp(L)$ expanded
-- statement:
--   Let $L = \sum_{n \ge 1} 2^{n^3} x^n / n$ over $\mathbb{Q}$, and let $\exp(L)$ be the composition of the exponential series with $L$. The coefficient of $x^2$ in $\exp(L)$ is:
--
--   $$[x^2] \exp(L) = [x^2] L + \frac{\left([x^1] L\right)^2}{2}.$$
--
--   Only the terms of degree at most $2$ in the exponential series contribute at degree $2$: the linear term contributes $[x^2]L$, and the quadratic term contributes half the coefficient of $x^2$ in $L^2$. With the earlier coefficient values this evaluates to $128 + 2^2/2 = 130$, the goal value.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib
import Definitions.Def_OeisA158110_Series
open PowerSeries

namespace OeisA158110

theorem coeff_two_subst_exp_logSeries :
    coeff 2 (subst (logSeries 2 3) (exp ℚ)) =
      coeff 2 (logSeries 2 3) + (coeff 1 (logSeries 2 3)) ^ 2 / 2 := by sorry

end OeisA158110
