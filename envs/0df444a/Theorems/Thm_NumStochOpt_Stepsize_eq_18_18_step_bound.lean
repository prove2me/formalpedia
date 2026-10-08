-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_eq_18_18_step_bound
-- name    : NumStochOpt.Stepsize.eq_18_18_step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:24:14.691548+00:00
-- url     : https://prove2.me/theorems/95103636-d04d-44d9-9c29-446cbf600a1c
-- title:
--   Eq. (18.18) — $\|x^{s+1}-x^s\|\le\|\rho_s\xi^s\|\le\rho_sC_2$
-- statement:
--   Let $X\subseteq\mathbb R^n$ be nonempty, closed and convex, $x^0\in X$, and
--   $$
--   x^{s+1}=\pi_X(x^s-\rho_s\xi^s),\qquad s=0,1,\dots
--   $$
--   with $\rho_s\ge0$ and $\|\xi^s\|\le C_2$ for all $s$. Then for every $s$
--   $$
--   \|x^{s+1}-x^s\|\le\|\rho_s\xi^s\|\le\rho_sC_2 .
--   $$
--
--   This is the step bound (18.18) in the proof of Theorem 2 of Chapter 18: it controls the inner product $\langle\xi^{s+1},x^s-x^{s+1}\rangle$ in the exponent of the adaptive stepsize rule (18.5).
--
--   **Formalization Note** The statement concerns one sample path; the book's "a.s." is the statement applied to almost every path, under (18.15) $\sup_s\|\xi^s\|<C_2$ a.s., which implies the hypothesis $\|\xi^s\|\le C_2$ here.
-- source:
--   S. Uryasev, "Adaptive Stochastic Quasigradient Procedures", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 18, p. 377, Eq. (18.18) (proof of Theorem 2)

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

namespace NumStochOpt.Stepsize

/-- **Eq. (18.18)** (Uryasev, Ch. 18 of Ermoliev & Wets (1988), p. 377, proof of Theorem 2): for
the projection method (18.2) on a nonempty closed convex `X ⊆ ℝⁿ` started in `X`, with
nonnegative stepsizes and directions bounded by `C₂` as in (18.15), every step is bounded by
`‖x^{s+1} - x^s‖ ≤ ‖ρ_s ξ^s‖ ≤ ρ_s C₂`. The statement is about one sample path. -/
theorem eq_18_18_step_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C₂ : ℝ)
    (hX_ne : X.Nonempty) (hX_closed : IsClosed X) (hX_conv : Convex ℝ X)
    (hx0 : x 0 ∈ X)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • ξ s))
    (hρ : ∀ s, 0 ≤ ρ s) (hξ : ∀ s, ‖ξ s‖ ≤ C₂) :
    ∀ s, ‖x (s + 1) - x s‖ ≤ ‖ρ s • ξ s‖ ∧ ‖ρ s • ξ s‖ ≤ ρ s * C₂ := by sorry

end NumStochOpt.Stepsize
