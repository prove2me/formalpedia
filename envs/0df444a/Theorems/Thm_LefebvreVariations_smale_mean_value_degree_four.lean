-- Prove2me | Theorems.Thm_LefebvreVariations_smale_mean_value_degree_four
-- name    : LefebvreVariations.smale_mean_value_degree_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:12:46.479394+00:00
-- url     : https://prove2.me/theorems/9bec0e10-e94f-50d1-a73d-3b96393465d3
-- title:
--   Lefebvre's variations, No. 88 — on a theme by Smale: Smale's mean value conjecture holds in degree four
-- statement:
--   Let $P\in\mathbb{C}[X]$ have degree exactly $4$ and let $z\in\mathbb{C}$ satisfy $P'(z)\ne0$. Then there is a critical point $c$ of $P$ (that is, $P'(c)=0$) such that
--   $$
--   \Bigl|\frac{P(z)-P(c)}{z-c}\Bigr| \;\le\; |P'(z)|.
--   $$
--
--   This is Smale's mean value conjecture with the constant $K=1$, restricted to degree $4$; the conjecture for all degrees is open. For degree $4$ it is a theorem (indeed the sharper constant $(d-1)/d=3/4$ is conjectured to suffice).
--
--   **Formalization Note** The statement is that of the platform's `SmaleMeanValue.smale_mean_value_conjecture` with the hypothesis `2 ≤ P.natDegree` replaced by `P.natDegree = 4`. The hypothesis $P'(z)\ne0$ makes $c\ne z$ for every critical point, so the quotient is a genuine difference quotient.
--
--   **Why this is a variation.** Variation on the open mission 'Smale's Mean Value Conjecture' (SmaleMeanValue.smale_mean_value_conjecture). It is the case of degree exactly 4 with the parent's own formulation and constant 1, the first degree beyond the elementary degrees 2 and 3; a finite-dimensional statement (five complex coefficients) that a prover can attack by reducing to normal forms.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   S. Smale, The fundamental theorem of algebra and complexity theory, Bull. Amer. Math. Soc. 4 (1981) 1-36 (the conjecture; low degrees). The conjecture with constant 1 is known for small degrees (I recall degrees up to 8, by Dubinin, Conte-Fujikawa-Lakic and others; exact attributions cited from memory and not re-checked). Truth check: the author tested 20000 random complex quartics and random points z by computer: the minimum over critical points c of |(P(z)-P(c))/(z-c)| / |P'(z)| was at most 0.7304, consistent with the conjectured sharp constant 3/4. Origin: the open mission 'Smale's Mean Value Conjecture' (theorem SmaleMeanValue.smale_mean_value_conjecture).

import Mathlib

set_option autoImplicit false

open Polynomial

namespace LefebvreVariations

/-- Smale's mean value conjecture with constant `1` for polynomials of degree exactly `4`. -/
theorem smale_mean_value_degree_four (P : ℂ[X]) (hP : P.natDegree = 4) (z : ℂ)
    (hz : P.derivative.eval z ≠ 0) :
    ∃ c : ℂ, P.derivative.eval c = 0 ∧
      ‖(P.eval z - P.eval c) / (z - c)‖ ≤ ‖P.derivative.eval z‖ := by
  sorry

end LefebvreVariations
