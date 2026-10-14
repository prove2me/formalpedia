-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_lemma_5_2_i
-- name    : MLLangevin.ConvexA1.lemma_5_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:07.28888+00:00
-- url     : https://prove2.me/theorems/e6d07fd7-ab65-4e7c-baaf-576a95738e3f
-- title:
--   Lemma 5.2 (i), p. 30 — one-step error 𝔼|X^x_γ − X̄^y_γ|² ≤ |x − y|²e^{−αγ} + (γ²L²/α)(γ|b(y)|² + σ²d)
-- statement:
--   Let $b$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$ with $0<\alpha\le L$, $\sigma>0$ and $W$ a standard $d$-dimensional Brownian motion. For $x,y\in\mathbb R^d$ let $X^x$ solve $X^x_t=x+\int_0^tb(X^x_s)\,ds+\sigma W_t$, and let $\bar X^y_t=y+t\,b(y)+\sigma W_t$ be one Euler step from $y$. For every $\gamma>0$,
--   $$\mathbb E\big[|X^x_\gamma-\bar X^y_\gamma|^2\big]\le|x-y|^2e^{-\alpha\gamma}+\frac{\gamma^2L^2}\alpha\big(\gamma|b(y)|^2+\sigma^2d\big).$$
--
--   Iterating this one-step estimate along the grid gives the uniform-in-time strong error bound of Proposition 5.1 (i).
--
--   **Formalization Note** The page states only "Let $\gamma>0$"; the standing hypotheses of §5.1 ($(\mathbf C_\alpha)$, $b$ $L$-Lipschitz, $0<\alpha\le L$, $\sigma>0$), which its proof uses, are carried as hypotheses. $X^x$ is any pathwise solution with continuous paths.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Lemma 5.2 (i), p. 30 (standing hypotheses of §5.1: (C_α), b L-Lipschitz, 0 < α ≤ L)

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Lemma 5.2 (i), p. 30: one-step L² error between the diffusion started at `x` and the
one-step Euler scheme `X̄^y_t = y + t b(y) + σ W_t` started at `y`, at time `γ`. -/
theorem lemma_5_2_i {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (hC : CondC b α) (hα : 0 < α) (hαL : α ≤ L) (hσ : 0 < σ)
    (x y : SDEState d) (X : ℝ≥0 → Ω → SDEState d) (hX : IsAddSolution b σ W x X)
    (γ : ℝ) (hγ : 0 < γ) :
    eLpNorm (fun ω => X γ.toNNReal ω - (y + γ • b y + σ • W γ.toNNReal ω)) 2 P ^ 2 ≤
      ENNReal.ofReal (‖x - y‖ ^ 2 * Real.exp (-α * γ) +
        γ ^ 2 * L ^ 2 / α * (γ * ‖b y‖ ^ 2 + σ ^ 2 * (d : ℝ))) := by sorry

end MLLangevin.ConvexA1
