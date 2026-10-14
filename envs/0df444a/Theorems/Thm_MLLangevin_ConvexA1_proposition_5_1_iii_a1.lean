-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_proposition_5_1_iii_a1
-- name    : MLLangevin.ConvexA1.proposition_5_1_iii_a1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:23.751092+00:00
-- url     : https://prove2.me/theorems/f6c3c939-0b45-4650-91ac-18980e1249cb
-- title:
--   Proposition 5.1 (iii), 𝔞 = 1, p. 33 — (H₂) holds with 𝔞 = 1 and c₂² ≲_uc L²α⁻³|b(x₀)|² + L²σ²α⁻²d
-- statement:
--   There is a universal constant $\mathfrak c_u$ such that the following holds. Let $d\ge1$, let $b$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$ with $0<\alpha\le L$, $\sigma>0$, $W$ a standard $d$-dimensional Brownian motion, $x_0\in\mathbb R^d$ and $\eta_0\in(0,\frac\alpha{2L^2}\wedge\frac12]$. Then there is $c_2>0$ such that, for every $\gamma\in(0,\eta_0]$ and $n\ge0$, the Euler schemes with steps $\gamma$ and $\gamma/2$ started at $x_0$ and driven by the same $W$ satisfy
--   $$\big\|\bar X^{\gamma,x_0}_{n\gamma}-\bar X^{\gamma/2,x_0}_{n\gamma}\big\|_2\le c_2\gamma^{1/2},\qquad c_2^2\le\mathfrak c_u\big(L^2\alpha^{-3}|b(x_0)|^2+L^2\sigma^2\alpha^{-2}d\big).$$
--
--   This is assumption $(\mathbf H_2)$ with $\mathfrak a=1$: it controls the variance of each correcting level of the multilevel estimator.
--
--   **Formalization Note** "$\lesssim_{uc}$" is an existential constant quantified before all data. The page does not name $\eta_0$; the range $(0,\frac\alpha{2L^2}\wedge\frac12]$ is the one Proposition 2.1 uses, and keeps both $\gamma$ and $\gamma/2$ inside the range of Proposition 5.1. $d\ge1$ is the paper's $\mathbb R^d$; at $d=0$ the right-hand side would be $0$ and no $c_2>0$ could satisfy it. The second line of (56) ($\mathfrak a=2$) belongs to the companion mission.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Proposition 5.1 (iii), first line of (56), p. 33

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Proposition 5.1 (iii), case `𝔞 = 1`, p. 33: (H₂) holds with `𝔞 = 1` and
`c₂² ≲_uc L²α⁻³|b(x₀)|² + L²σ²α⁻²d`, for every `η₀ ∈ (0, α/(2L²) ∧ 1/2]`. -/
theorem proposition_5_1_iii_a1 : ∃ cu : ℝ, ∀ {d : ℕ} (_hd : 0 < d) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d)
    (_hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (_hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (_hC : CondC b α) (_hα : 0 < α) (_hαL : α ≤ L) (_hσ : 0 < σ) (x₀ : SDEState d)
    (η₀ : ℝ) (_hη₀ : 0 < η₀) (_hη₀' : η₀ ≤ min (α / (2 * L ^ 2)) (1 / 2)),
    ∃ c₂ : ℝ, H2 P b σ W x₀ η₀ 1 c₂ ∧
      c₂ ^ 2 ≤ cu * (L ^ 2 * α⁻¹ ^ 3 * ‖b x₀‖ ^ 2 + L ^ 2 * σ ^ 2 * α⁻¹ ^ 2 * (d : ℝ)) := by sorry

end MLLangevin.ConvexA1
