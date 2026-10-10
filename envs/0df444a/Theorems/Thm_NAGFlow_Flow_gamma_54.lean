-- Prove2me | Theorems.Thm_NAGFlow_Flow_gamma_54
-- name    : NAGFlow.Flow.gamma_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:37:40.649275+00:00
-- url     : https://prove2.me/theorems/cb72291d-d6c0-458f-b00b-cc3b34d91726
-- title:
--   (54), p. 12 — γ(t) = μ + (γ₀ − μ)e^{−t} is the solution of γ′ = μ − γ, γ(0) = γ₀, is positive, and tends to μ monotonically and exponentially
-- statement:
--   Let $\mu\ge0$ and $\gamma_0>0$, and set
--   $$\gamma(t)=\mu+(\gamma_0-\mu)e^{-t}.$$
--   Then:
--   1. $\gamma(0)=\gamma_0$ and $\gamma'(t)=\mu-\gamma(t)$ for every $t\in\mathbb R$, so $\gamma$ solves (54);
--   2. it is the only solution of (54) on $[0,\infty)$: any function $\tilde\gamma$ with $\tilde\gamma(0)=\gamma_0$ and $\tilde\gamma'(t)=\mu-\tilde\gamma(t)$ for $t\ge0$ (right derivative at $0$) coincides with $\gamma$ on $[0,\infty)$;
--   3. $\gamma(t)>0$ for all $t\ge0$;
--   4. $\gamma$ is monotone on $[0,\infty)$ (nondecreasing or nonincreasing), $\gamma(t)\to\mu$ as $t\to+\infty$, and the convergence is exponential: $|\gamma(t)-\mu|=|\gamma_0-\mu|\,e^{-t}$.
--
--   The function $\gamma$ is the time-dependent scaling factor of the NAG flow; its positivity is what makes the system (56) an ordinary differential equation for all $t\ge0$, including the convex case $\mu=0$, where $\gamma(t)=\gamma_0e^{-t}\to0$.
--
--   **Formalization Note.** "Converges exponentially and monotonically" is stated as the disjunction of `MonotoneOn` and `AntitoneOn` on $[0,\infty)$, the limit at `atTop`, and the exact identity for $|\gamma(t)-\mu|$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, §3.1, (54) and the two sentences after it, p. 12

import Mathlib
import Definitions.Def_NAGFlow_Flow_Setting

namespace NAGFlow.Flow

open Set Filter Topology

/-- §3.1, (54) and the two sentences after it, p. 12. Let `μ ≥ 0` and `γ₀ > 0`. The function
`γ(t) = μ + (γ₀ − μ)e^{−t}` solves (54) `γ′ = μ − γ`, `γ(0) = γ₀`, and is its only solution on
`[0, ∞)`; moreover `γ(t) > 0` for all `t ≥ 0`, and `γ(t)` converges to `μ` monotonically as
`t → +∞` (exponentially: `|γ(t) − μ| = |γ₀ − μ| e^{−t}`). -/
theorem gamma_54 (μ γ₀ : ℝ) (hμ : 0 ≤ μ) (hγ₀ : 0 < γ₀) :
    gammaFn μ γ₀ 0 = γ₀ ∧
    (∀ t : ℝ, HasDerivAt (gammaFn μ γ₀) (μ - gammaFn μ γ₀ t) t) ∧
    (∀ γ : ℝ → ℝ, γ 0 = γ₀ →
      (∀ t, 0 ≤ t → HasDerivWithinAt γ (μ - γ t) (Ici 0) t) →
      EqOn γ (gammaFn μ γ₀) (Ici 0)) ∧
    (∀ t : ℝ, 0 ≤ t → 0 < gammaFn μ γ₀ t) ∧
    (MonotoneOn (gammaFn μ γ₀) (Ici 0) ∨ AntitoneOn (gammaFn μ γ₀) (Ici 0)) ∧
    Tendsto (gammaFn μ γ₀) atTop (𝓝 μ) ∧
    (∀ t : ℝ, |gammaFn μ γ₀ t - μ| = |γ₀ - μ| * Real.exp (-t)) := by sorry

end NAGFlow.Flow
