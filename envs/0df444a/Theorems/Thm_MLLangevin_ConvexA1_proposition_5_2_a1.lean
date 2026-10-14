-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_proposition_5_2_a1
-- name    : MLLangevin.ConvexA1.proposition_5_2_a1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:31.076496+00:00
-- url     : https://prove2.me/theorems/ec16917a-2c20-44db-82b2-67f52b0628b5
-- title:
--   Proposition 5.2, 𝔞 = 1, δ = 1/2, p. 35 — |π(f) − π^γ(f)| ≤ √(β₁(x⋆)γ) for 1-Lipschitz f, i.e. 𝒲₁(π, π^γ) ≤ √(β₁(x⋆)γ)
-- statement:
--   Let $b$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$ with $0<\alpha\le L$, $\sigma>0$ and $W$ a standard $d$-dimensional Brownian motion. Let $\pi$ be an invariant probability of the diffusion $X^x_t=x+\int_0^tb(X^x_s)ds+\sigma W_t$, and, for $\gamma\in(0,\alpha/(2L^2)]$, let $\pi^\gamma$ be an invariant probability of the Euler scheme with step $\gamma$. Then for every $x^\star\in\mathbb R^d$ and every $1$-Lipschitz $f:\mathbb R^d\to\mathbb R$ integrable under $\pi$ and $\pi^\gamma$,
--   $$|\pi(f)-\pi^\gamma(f)|\le\sqrt{\beta_1(x^\star)\gamma},$$
--   with $\beta_1$ as in Proposition 5.1. Taking the supremum over such $f$, this is $\mathcal W_1(\pi,\pi^\gamma)\le\sqrt{\beta_1(x^\star)\gamma}$ by Kantorovich–Rubinstein duality.
--
--   This is the bias estimate $(\mathbf H_3)$ with $\delta=\frac12$.
--
--   **Formalization Note** $\mathcal W_1$ is not available in Mathlib; the statement uses its dual form, which is exactly how the proof and $(\mathbf H_3)$ use it. The step range is the page's $(0,\alpha/(2L^2)]$ (Proposition 5.1 is stated for $\gamma<1$ as well, but its proof of (i) uses only $\gamma\le\alpha/(2L^2)$). The page's closing sentence giving an explicit $c_3^2$ is not formalized (that value does not follow from the displayed bound).
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Proposition 5.2, case 𝔞 = 1 and δ = 1/2, p. 35

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Proposition 5.2, case `𝔞 = 1, δ = 1/2`, p. 35, in Kantorovich–Rubinstein form:
`|π(f) − π^γ(f)| ≤ √(β₁(x⋆)γ)` for every 1-Lipschitz `f`, i.e. `𝒲₁(π, π^γ) ≤ √(β₁(x⋆)γ)`. -/
theorem proposition_5_2_a1 {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (hC : CondC b α) (hα : 0 < α) (hαL : α ≤ L) (hσ : 0 < σ)
    (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d) (hX : ∀ x, IsAddSolution b σ W x (Xsol x))
    (π : Measure (SDEState d)) [IsProbabilityMeasure π] (hπ : IsInvDiffusion P Xsol π)
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ ≤ α / (2 * L ^ 2))
    (πγ : Measure (SDEState d)) [IsProbabilityMeasure πγ] (hπγ : IsInvChain P b σ γ W πγ)
    (xs : SDEState d) (f : SDEState d → ℝ) (hf : LipschitzWith 1 f)
    (hfπ : Integrable f π) (hfπγ : Integrable f πγ) :
    |(∫ y, f y ∂π) - ∫ y, f y ∂πγ| ≤ Real.sqrt (beta1 b σ α L xs xs * γ) := by sorry

end MLLangevin.ConvexA1
