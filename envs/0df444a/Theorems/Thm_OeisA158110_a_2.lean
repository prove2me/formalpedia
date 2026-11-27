-- Prove2me | Theorems.Thm_OeisA158110_a_2
-- name    : OeisA158110.a_2
-- status  : Open
-- author  : @pageman
-- created : 2026-11-27T05:28:57.355084+00:00
-- url     : https://prove2.me/theorems/dd13b7ad-7b1e-5431-ad4c-f2dcd541aa88
-- title:
--   OEIS A158110: $a(2) = 130$
-- statement:
--   The sequence A158110 lists the coefficients of $\exp\!\left(\sum_{n \ge 1} 2^{n^3} x^n / n\right)$. Its third term is $130$:
--
--   $$a(2) = 130.$$
--
--   This is the goal of the mission. The value is a finite computation from the coefficients of the auxiliary series at degrees $1$ and $2$, assembled by the mission's milestone identities.
-- source:
--   OEIS A158110, Paul D. Hanna, 2009, https://oeis.org/A158110 — the sequence of coefficients of exp(sum_{n>=1} 2^(n^3) x^n / n). Lean source transplanted verbatim (definitions and theorem statements) from google-deepmind/formal-conjectures, FormalConjectures/OEIS/158110.lean, commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53. Integrality conjecture in A158110 proved by Sela Fried, 'Proof of a conjecture stated in A158110', 2025, https://oeis.org/A158110/a158110.pdf

import Mathlib
import Definitions.Def_OeisA158110_Series

namespace OeisA158110

theorem a_2 : a 2 = 130 := by sorry

end OeisA158110
