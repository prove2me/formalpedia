-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_thm2_step1_stepsizes_not_summable
-- name    : NumStochOpt.Stepsize.thm2_step1_stepsizes_not_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:24:22.072426+00:00
-- url     : https://prove2.me/theorems/749e1329-6603-427b-95ca-d58767d539b7
-- title:
--   Proof of Ch. 18 Theorem 2, step 1 — the adaptive stepsizes (18.5) satisfy $\sum\rho_s=\infty$
-- statement:
--   Let $X\subseteq\mathbb R^n$ be nonempty, closed and convex, $a>1$, $\delta>0$, and consider one path of the method
--   $$
--   x^{s+1}=\pi_X(x^s-\rho_s\xi^s),\qquad \rho_{s+1}=\rho_s\,a^{\langle\xi^{s+1},x^s-x^{s+1}\rangle-\delta\rho_s},\qquad s=0,1,\dots
--   $$
--   (Eqs. (18.2) and (18.5)), with $x^0\in X$, $\rho_0>0$ and $\|\xi^s\|\le C_2$ for all $s$. Then
--   $$
--   \sum_{s=0}^\infty\rho_s=\infty .
--   $$
--
--   This is the first step of the proof of Theorem 2: the adaptive stepsizes satisfy condition (18.13) of Theorem 1. The term $-\delta\rho_s$ in the exponent pushes the stepsizes down; this step shows it cannot push them down fast enough to make them summable.
--
--   **Formalization Note** The stepsize rule is the second form of (18.5), $\rho_{s+1}=\rho_s a^{\langle\xi^{s+1},x^s-x^{s+1}\rangle-\delta\rho_s}$; the first form $\rho_s a^{\rho_s\langle\xi^{s+1},\xi^s\rangle-\delta\rho_s}$ agrees with it only when the projection is inactive, and the proof uses the second. The power is the real power `Real.rpow`. The statement is pathwise; the book's "a.s." follows from (18.15).
-- source:
--   S. Uryasev, "Adaptive Stochastic Quasigradient Procedures", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 18, p. 377, proof of Theorem 2, step 1, with (18.5) p. 375

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

open Filter Topology
open scoped InnerProductSpace

namespace NumStochOpt.Stepsize

/-- **Proof of Theorem 2, step 1** (Uryasev, Ch. 18 of Ermoliev & Wets (1988), p. 377): the
adaptive stepsizes of rule (18.5) are not summable, i.e. condition (18.13) of Theorem 1 holds.

On one sample path: `X ⊆ ℝⁿ` nonempty closed convex, `x⁰ ∈ X`, `x^{s+1} = π_X(x^s - ρ_s ξ^s)`
(18.2), `ρ_{s+1} = ρ_s a^{⟨ξ^{s+1}, x^s - x^{s+1}⟩ - δ ρ_s}` (18.5, second form) with `a > 1`,
`δ > 0`, `ρ₀ > 0`, and `‖ξ^s‖ ≤ C₂` for all `s` (18.15). Then `∑_{s=0}^∞ ρ_s = ∞`. -/
theorem thm2_step1_stepsizes_not_summable {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (a δ C₂ : ℝ)
    (hX_ne : X.Nonempty) (hX_closed : IsClosed X) (hX_conv : Convex ℝ X)
    (ha : 1 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ 0)
    (hx0 : x 0 ∈ X)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • ξ s))
    (hrule : ∀ s, ρ (s + 1) = ρ s * a ^ (⟪ξ (s + 1), x s - x (s + 1)⟫_ℝ - δ * ρ s))
    (hξ : ∀ s, ‖ξ s‖ ≤ C₂) :
    Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s) atTop atTop := by sorry

end NumStochOpt.Stepsize
