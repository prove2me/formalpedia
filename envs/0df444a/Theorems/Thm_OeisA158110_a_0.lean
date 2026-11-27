-- Prove2me | Theorems.Thm_OeisA158110_a_0
-- name    : OeisA158110.a_0
-- status  : Open
-- author  : @pageman
-- created : 2026-11-27T05:22:56.885042+00:00
-- url     : https://prove2.me/theorems/94f13677-9cf5-4cfe-93c1-80ceffd7501c
-- title:
--   OEIS A158110: $a(0) = 1$
-- statement:
--   The sequence A158110 lists the coefficients of $\exp\!\left(\sum_{n \ge 1} 2^{n^3} x^n / n\right)$. Its constant term is $1$:
--
--   $$a(0) = 1.$$
--
--   A power series with constant term $0$ composed into the exponential series gives constant term $\exp(0) = 1$. This is the first term of the sequence and a check that the formalization reads the series correctly at degree $0$.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib
import Definitions.Def_OeisA158110_Series

namespace OeisA158110

theorem a_0 : a 0 = 1 := by sorry

end OeisA158110
