-- Prove2me | Theorems.Thm_MetodosNumericos_interpolating_polynomial_unique
-- name    : MetodosNumericos.interpolating_polynomial_unique
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:51:18.661686+00:00
-- url     : https://prove2.me/theorems/62221bea-dbcd-4360-a5ca-783422805565
-- title:
--   Existence and uniqueness of the interpolating polynomial
-- statement:
--   Given $n+1$ points with pairwise distinct abscissas, there is exactly one real polynomial of degree at most $n$ passing through them. This is Proposição 7.2.1.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 7, Proposição 7.2.1, pp. 136–138.

import Mathlib

namespace MetodosNumericos

theorem interpolating_polynomial_unique {n : ℕ} (xs fs : Fin (n + 1) → ℝ)
    (hxs : Function.Injective xs) :
    ∃! p : Polynomial ℝ, p.degree ≤ (n : ℕ) ∧ ∀ i, p.eval (xs i) = fs i := by sorry

end MetodosNumericos
