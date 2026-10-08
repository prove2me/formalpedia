-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_thm2_step2_stepsizes_tend_to_zero
-- name    : NumStochOpt.Stepsize.thm2_step2_stepsizes_tend_to_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:24:41.062386+00:00
-- url     : https://prove2.me/theorems/f0570538-00f0-455f-840f-ed6d1f114e02
-- title:
--   Proof of Ch. 18 Theorem 2, step 2 — under (18.17) the adaptive stepsizes tend to $0$
-- statement:
--   Let $F$ be convex on an open convex set $U\subseteq\mathbb R^n$ that contains the convex compact set $X$, and write $\partial F(x)$ for the set of subgradients of $F$ at $x$. Let $a>1$, $\delta>0$ and consider one path of
--   $$
--   x^{s+1}=\pi_X(x^s-\rho_s\xi^s),\qquad \rho_{s+1}=\rho_s\,a^{\langle\xi^{s+1},x^s-x^{s+1}\rangle-\delta\rho_s}
--   $$
--   with $x^0\in X$, $\rho_0>0$ and $\|\xi^s\|\le C_2$ for all $s$. Put $C_s=\inf_{h\in\partial F(x^s)}\|\xi^s-h\|$. If
--   $$
--   \delta>C_2\,\limsup_{s\to\infty}C_s ,
--   $$
--   then $\rho_s\to0$.
--
--   This is condition (18.12) of Theorem 1 for the adaptive rule: the stepsizes shrink as long as the directions $\xi^s$ stay close enough to true subgradients, measured against $\delta$.
--
--   **Formalization Note** The page's condition (18.17) prints $\delta>C_1\limsup C_s$ with the diameter $C_1$ of $X$. The proof's estimate (via (18.18), $\|x^s-x^{s+1}\|\le\rho_sC_2$) produces $(C_2C_s-\delta)\rho_s$ in the exponent, and only the constant $C_2$ makes the condition invariant under rescaling of $\mathbb R^n$ (with $C_1$, a change of scale turns any path with any $\delta>0$ into one that meets the condition, so the printed condition would impose no restriction); the statement uses $C_2$. The $\limsup$ condition is written as: some $L$ with $C_2L<\delta$ bounds $C_s$ for all large $s$. $\partial F(x^s)$ is nonempty because $F$ is convex on the open set $U\ni x^s$, so the infimum is not the junk value of an empty set. The statement is pathwise.
-- source:
--   S. Uryasev, "Adaptive Stochastic Quasigradient Procedures", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 18, p. 378, proof of Theorem 2, step 2, with (18.17) p. 377

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

open Filter Topology
open scoped InnerProductSpace

namespace NumStochOpt.Stepsize

/-- **Proof of Theorem 2, step 2** (Uryasev, Ch. 18 of Ermoliev & Wets (1988), p. 378): the
adaptive stepsizes of rule (18.5) tend to zero, i.e. condition (18.12) of Theorem 1 holds.

On one sample path: `F` is convex on an open convex `U ⊆ ℝⁿ` containing the convex compact `X`,
`∂F(x)` is its set of subgradients at `x`, `x⁰ ∈ X`, `x^{s+1} = π_X(x^s - ρ_s ξ^s)` (18.2),
`ρ_{s+1} = ρ_s a^{⟨ξ^{s+1}, x^s - x^{s+1}⟩ - δ ρ_s}` (18.5, second form) with `a > 1`, `δ > 0`,
`ρ₀ > 0`, `‖ξ^s‖ ≤ C₂` for all `s` (18.15), and
`δ > C₂ · limsup_s inf_{h ∈ ∂F(x^s)} ‖ξ^s - h‖` (18.17, with the constant `C₂` of (18.15) that
the proof's estimate (18.18) produces; the page prints `C₁`). The `limsup` condition is written
out as: some `L` with `C₂ L < δ` eventually bounds `inf_{h ∈ ∂F(x^s)} ‖ξ^s - h‖`.
Then `ρ_s → 0`. -/
theorem thm2_step2_stepsizes_tend_to_zero {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (U X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (a δ C₂ : ℝ)
    (hU_open : IsOpen U) (hU_conv : Convex ℝ U) (hXU : X ⊆ U)
    (hX_conv : Convex ℝ X) (hX_cpt : IsCompact X) (hF_conv : ConvexOn ℝ U F)
    (ha : 1 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ 0)
    (hx0 : x 0 ∈ X)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • ξ s))
    (hrule : ∀ s, ρ (s + 1) = ρ s * a ^ (⟪ξ (s + 1), x s - x (s + 1)⟫_ℝ - δ * ρ s))
    (hξ : ∀ s, ‖ξ s‖ ≤ C₂)
    (h1817 : ∃ L, C₂ * L < δ ∧
      ∀ᶠ s in atTop, Metric.infDist (ξ s) (subdiffOn U F (x s)) ≤ L) :
    Tendsto ρ atTop (𝓝 0) := by sorry

end NumStochOpt.Stepsize
