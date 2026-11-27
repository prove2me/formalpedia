-- Prove2me | Theorems.Thm_OeisA158110_a_1
-- name    : OeisA158110.a_1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-27T05:26:00.640801+00:00
-- url     : https://prove2.me/theorems/0f31cacd-6d6d-598f-947b-3cbc8bf67f14
-- title:
--   OEIS A158110: $a(1) = 2$
-- statement:
--   The sequence A158110 lists the coefficients of $\exp\!\left(\sum_{n \ge 1} 2^{n^3} x^n / n\right)$. Its second term is $2$:
--
--   $$a(1) = 2.$$
--
--   At degree $1$ only the linear term of the exponential series contributes, so this value equals the coefficient of $x$ in the auxiliary series. This is the second term of the sequence and a check that the formalization reads the series correctly at degree $1$.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib
import Definitions.Def_OeisA158110_Series

namespace OeisA158110

theorem a_1 : a 1 = 2 := by sorry

end OeisA158110
