-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_ell_deriv_sq_bounds
-- name    : OTDRO.StrongCvx.ell_deriv_sq_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:24.40588+00:00
-- url     : https://prove2.me/theorems/056edad3-3343-4777-a986-8cfc17b808c1
-- title:
--   Lemma 6, p. 33 — uniform positive bounds on E[ℓ′²]
-- statement:
--   Let $P_0$ be a probability law, $B\subseteq\mathbb R^d$ nonempty, convex and compact, and let the loss satisfy Assumptions 2–3. There are positive constants $\underline L$ and $\overline L$ such that, for every $\beta\in B$,
--
--   $$\underline L\le\mathbb E_{P_0}\!\left[\ell'(\beta^{\mathsf T}X)^2\right]\le\overline L.$$
--
--   The bounds provide the constants that define the optimizer region and the strong-convexity radius.
--
--   **Formalization Note** Integrability of the squared derivative is stated along with its bounds, and nonemptiness of $B$ makes its radius and the uniform bound nonvacuous.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Lemma 6, p. 33

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Assumptions

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Lemma 6, p. 33: the squared derivative has positive uniform lower
and finite upper expectation bounds over B. -/
theorem ell_deriv_sq_bounds {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB4 : Assumption4 B)
    (hBne : B.Nonempty) (M : ℝ) (h3 : Assumption3 P0 ℓ B M) :
    ∃ Llow Lbar : ℝ, DerivSqBounds P0 ℓ B Llow Lbar := by sorry

end OTDRO.StrongCvx
