-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_proposition_5_2_a2
-- name    : MLLangevin.ConvexA2.proposition_5_2_a2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:40.497567+00:00
-- url     : https://prove2.me/theorems/187c3de0-7ff2-415c-a7cb-7f20ea1019fe
-- title:
--   Proposition 5.2, 𝔞 = 2, δ = 1, p. 35 — 𝒲₁(π, π^γ) ≤ √(β₂(x⋆)) γ, read through Lipschitz test functions
-- statement:
--   Assume $(\mathbf C_\alpha)$, that $b$ is $L$-Lipschitz with $0<\alpha\le L$ and $\mathcal C^2$ with bounded partial derivatives up to order 2, and $\sigma>0$. Let $W$ be a standard $d$-dimensional Brownian motion, $X^x$ the solution of $X^x_t=x+\int_0^tb(X^x_s)ds+\sigma W_t$ for each $x$, and $\pi$ a probability measure invariant for this diffusion. Let $\gamma\in(0,\frac{\alpha}{2L^2}]$ with $\gamma<1$ and let $\pi^\gamma$ be an invariant probability of the Euler chain with step $\gamma$. Then for every $x^\star\in\mathbb R^d$ and every Lipschitz $f:\mathbb R^d\to\mathbb R$ with $[f]_1\le1$, integrable for $\pi$ and $\pi^\gamma$,
--   $$|\pi(f)-\pi^\gamma(f)|\le\sqrt{\beta_2(x^\star)}\,\gamma,$$
--   with $\beta_2$ as in Proposition 5.1(ii). Equivalently, $\mathcal W_1(\pi,\pi^\gamma)\le\sqrt{\beta_2(x^\star)}\gamma$.
--
--   This bias bound of order one in the step yields $(\mathbf H_3)$ with $\delta=1$.
--
--   **Formalization Note** $\mathcal W_1$ is not in Mathlib; the statement uses its Kantorovich–Rubinstein form $\mathcal W_1(\pi,\pi^\gamma)=\sup_{[f]_1\le1}|\pi(f)-\pi^\gamma(f)|$, which is how the proof and $(\mathbf H_3)$ use it. The page's case $\mathfrak a=1,\delta=\frac12$ belongs to the companion mission. The hypothesis $\gamma<1$ is added: the proof applies Proposition 5.1, which requires it. The regularity of §2.4.2 and $\sigma>0$ are carried as in Proposition 5.1(ii). The page's subsequent value of $c_3^2$ is not part of this item.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Proposition 5.2 (case 𝔞 = 2, δ = 1), p. 35

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem proposition_5_2_a2 {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ)
    (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) (hC : MLLangevin.ConvexA1.CondC b α) (hα : 0 < α) (hαL : α ≤ L)
    (hb2 : C2Bounded b) (hσ : 0 < σ)
    (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d) (hX : ∀ x, IsAddSolution b σ W x (Xsol x))
    (π : Measure (SDEState d)) [IsProbabilityMeasure π] (hπ : IsInvDiffusion P Xsol π)
    (γ : ℝ) (hγ : 0 < γ) (hγη : γ ≤ α / (2 * L ^ 2)) (hγ1 : γ < 1)
    (πγ : Measure (SDEState d)) [IsProbabilityMeasure πγ] (hπγ : IsInvChain b σ γ πγ)
    (xs : SDEState d) (f : SDEState d → ℝ) (hf : ∃ K, LipschitzWith K f) (hf1 : MLLangevin.ConvexA1.lipConst f ≤ 1)
    (hfπ : Integrable f π) (hfπγ : Integrable f πγ) :
    |∫ x, f x ∂π - ∫ x, f x ∂πγ| ≤ Real.sqrt (beta2 b σ α L xs xs) * γ := by sorry

end MLLangevin.ConvexA2
