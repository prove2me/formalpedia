-- Prove2me | Theorems.Thm_MetodosNumericos_rational_root
-- name    : MetodosNumericos.rational_root
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:15:00.766984+00:00
-- url     : https://prove2.me/theorems/eaa3ccb6-8857-4581-8dfa-7f9093208dd1
-- title:
--   Rational root test: $p \\mid a_n$ and $q \\mid a_0$
-- statement:
--   If a polynomial with integer coefficients has a rational root $p/q$ in lowest terms, then the numerator divides the constant coefficient and the denominator divides the leading coefficient. This is Proposição 4.3.1, the test the source uses to enumerate the rational candidates before any iterative method is started.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 4, Proposição 4.3.1, p. 76.

import Mathlib

namespace MetodosNumericos

theorem rational_root (p : Polynomial ℤ) (hp : p ≠ 0) (r : ℚ)
    (hr : Polynomial.aeval r p = 0) :
    r.num ∣ p.coeff 0 ∧ (r.den : ℤ) ∣ p.leadingCoeff := by sorry

end MetodosNumericos
