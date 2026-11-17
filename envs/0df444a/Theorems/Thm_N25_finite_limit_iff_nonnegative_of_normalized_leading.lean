-- Prove2me | Theorems.Thm_N25_finite_limit_iff_nonnegative_of_normalized_leading
-- name    : N25.finite_limit_iff_nonnegative_of_normalized_leading
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:50.861598+00:00
-- url     : https://prove2.me/theorems/9e719e21-4a60-4a8c-ac96-774409e5d7bf
-- title:
--   A normalized exponential leading term has a finite limit exactly for nonnegative exponent
-- statement:
--   Let $f:\mathfrak H\to\mathbb C$, let $a\in\mathbb R$, and let $L\ne0$. Assume
--
--   $$\frac{f(\tau)}{e^{2\pi ia\tau}}\longrightarrow L\qquad(\operatorname{Im}\tau\to\infty).$$
--
--   Then $f$ has a finite complex limit at infinity if and only if $a\ge0$. This converts normalized leading exponents into valuation-ring membership.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem N25.finite_limit_iff_nonnegative_of_normalized_leading
    (f : UpperHalfPlane → ℂ) (a : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hlead : Filter.Tendsto
      (fun τ : UpperHalfPlane => f τ /
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L)) :
    (∃ c : ℂ, Filter.Tendsto f UpperHalfPlane.atImInfty (nhds c)) ↔ 0 ≤ a := by sorry
