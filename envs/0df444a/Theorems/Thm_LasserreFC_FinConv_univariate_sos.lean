-- Prove2me | Theorems.Thm_LasserreFC_FinConv_univariate_sos
-- name    : LasserreFC.FinConv.univariate_sos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:30:26.175568+00:00
-- url     : https://prove2.me/theorems/935a9bf5-b989-46fa-9aa7-25be62e7b9a6
-- title:
--   Proof of Theorem 1.1, p. 8 — s(t) = 1 + t + c t^{2e} is SOS for some c > 0
-- statement:
--   Let $e \ge 1$ be an integer. Then there is a constant $c > 0$ such that the univariate polynomial
--
--   $$s(t) = 1 + t + c\, t^{2e}$$
--
--   is a sum of squares of polynomials in $\mathbb R[t]$.
--
--   In the proof of Theorem 1.1 (citing [22, Lemma 2.1]) the polynomial $\varepsilon\, s(\hat f/\varepsilon)$ supplies an SOS certificate whose degree does not depend on $\varepsilon$.
--
--   **Formalization Note** The page writes the exponent as $2\ell$ and leaves $\ell \ge 1$ implicit: for $\ell = 0$, $s$ has degree one and is not SOS. The statement is the page's existence of a suitable $c$.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 8, proof of Theorem 1.1 ([22, Lemma 2.1])

import Mathlib

namespace LasserreFC.FinConv

open Polynomial

/-- Proof of Theorem 1.1, p. 8 ([22, Lemma 2.1]): for `e ≥ 1` there is `c > 0` such that the univariate
polynomial `s(t) = 1 + t + c t^{2e}` is a sum of squares in `ℝ[t]`. -/
theorem univariate_sos (e : ℕ) (he : 1 ≤ e) :
    ∃ c : ℝ, 0 < c ∧ IsSumSq (1 + X + C c * X ^ (2 * e) : ℝ[X]) := by sorry

end LasserreFC.FinConv
