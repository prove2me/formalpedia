-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_thm2_step2_stepsize_ratio_to_one
-- name    : NumStochOpt.Stepsize.thm2_step2_stepsize_ratio_to_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:24:28.009982+00:00
-- url     : https://prove2.me/theorems/e8a32350-8144-4872-ab88-76c134f965d7
-- title:
--   Proof of Ch. 18 Theorem 2, end of step 2 — $\rho_{s+1}/\rho_s\to1$
-- statement:
--   Let $X\subseteq\mathbb R^n$ be nonempty, closed and convex, $a>1$, $\delta>0$, and consider one path of
--   $$
--   x^{s+1}=\pi_X(x^s-\rho_s\xi^s),\qquad \rho_{s+1}=\rho_s\,a^{\langle\xi^{s+1},x^s-x^{s+1}\rangle-\delta\rho_s}
--   $$
--   with $x^0\in X$, $\rho_0>0$ and $\|\xi^s\|\le C_2$ for all $s$. If $\rho_s\to0$, then
--   $$
--   \frac{\rho_{s+1}}{\rho_s}\longrightarrow1 .
--   $$
--
--   This verifies condition (2) of Theorem 1 of Chapter 18 for the adaptive rule (18.5), whose stepsize $\rho_{s+1}$ depends on the direction $\xi^{s+1}$ and therefore does not fall under condition (1).
--
--   **Formalization Note** The page prints the conclusion as $\rho_{s+1}/\rho_s\to0$; condition (2) of Theorem 1, which this step checks, requires $\to1$, and $\to0$ would contradict $\sum\rho_s=\infty$. The statement is pathwise.
-- source:
--   S. Uryasev, "Adaptive Stochastic Quasigradient Procedures", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 18, p. 378, proof of Theorem 2, final displays

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

open Filter Topology
open scoped InnerProductSpace

namespace NumStochOpt.Stepsize

/-- **Proof of Theorem 2, end of step 2** (Uryasev, Ch. 18 of Ermoliev & Wets (1988), p. 378):
under the adaptive rule (18.5), stepsizes that tend to zero have consecutive ratios tending to
one, which is condition (2) of Theorem 1 (the page prints `ρ_{s+1}/ρ_s → 0`).

On one sample path: `X ⊆ ℝⁿ` nonempty closed convex, `x⁰ ∈ X`, `x^{s+1} = π_X(x^s - ρ_s ξ^s)`
(18.2), `ρ_{s+1} = ρ_s a^{⟨ξ^{s+1}, x^s - x^{s+1}⟩ - δ ρ_s}` (18.5, second form) with `a > 1`,
`δ > 0`, `ρ₀ > 0`, `‖ξ^s‖ ≤ C₂` for all `s` (18.15). If `ρ_s → 0`, then `ρ_{s+1}/ρ_s → 1`. -/
theorem thm2_step2_stepsize_ratio_to_one {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (a δ C₂ : ℝ)
    (hX_ne : X.Nonempty) (hX_closed : IsClosed X) (hX_conv : Convex ℝ X)
    (ha : 1 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ 0)
    (hx0 : x 0 ∈ X)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • ξ s))
    (hrule : ∀ s, ρ (s + 1) = ρ s * a ^ (⟪ξ (s + 1), x s - x (s + 1)⟫_ℝ - δ * ρ s))
    (hξ : ∀ s, ‖ξ s‖ ≤ C₂)
    (hρ_lim : Tendsto ρ atTop (𝓝 0)) :
    Tendsto (fun s => ρ (s + 1) / ρ s) atTop (𝓝 1) := by sorry

end NumStochOpt.Stepsize
