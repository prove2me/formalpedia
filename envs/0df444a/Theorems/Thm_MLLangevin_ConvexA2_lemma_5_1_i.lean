-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_lemma_5_1_i
-- name    : MLLangevin.ConvexA2.lemma_5_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:41.351078+00:00
-- url     : https://prove2.me/theorems/d1f38362-e735-4286-8adf-f12b8e0fb7f9
-- title:
--   Lemma 5.1 (i), p. 28 — 𝔼|X̄^{γ,x}_t − x⋆|² ≤ |x − x⋆|²e^{−αt/2} + |b(x⋆)|²(1/L² + 2/α²) + 2σ²d/α, and π^γ exists and is unique
-- statement:
--   Assume $(\mathbf C_\alpha)$, that $b$ is $L$-Lipschitz with $0<\alpha\le L$, and $\sigma>0$. Let $W$ be a standard $d$-dimensional Brownian motion and $x^\star\in\mathbb R^d$. For $\gamma>0$ let $\bar X^{\gamma,x}$ be the continuous-time Euler scheme with step $\gamma$, started at $x$ and driven by $W$.
--
--   1. For every $\gamma\in(0,\alpha/(2L^2)]$, every $t\ge0$ and every $x\in\mathbb R^d$,
--   $$\mathbb E\big[|\bar X^{\gamma,x}_t-x^\star|^2\big]\le|x-x^\star|^2e^{-\frac\alpha2t}+|b(x^\star)|^2\Big(\frac1{L^2}+\frac2{\alpha^2}\Big)+\frac{2\sigma^2d}{\alpha}. \tag{47}$$
--   2. For every $\gamma\in(0,\alpha/(2L^2)]$, the Euler chain with step $\gamma$ has exactly one invariant probability distribution $\pi^\gamma$.
--
--   The uniform second-moment bound (47) controls the scheme over infinite horizons; it is the source of the bounds $(\mathbf H_1)$ and $(\mathbf H_4)$ and of the moment estimate (57) used in Proposition 5.1.
--
--   **Formalization Note** The expectation is the square of the $L^2(\mathbb P)$ norm in $[0,\infty]$. The hypothesis $\sigma>0$ is the standing assumption of §2.4 (p. 9), on which uniqueness of $\pi^\gamma$ rests. The displayed bound on $\sup_\gamma\pi^\gamma(|\cdot-x^\star|^2)$ that follows (47) on p. 28 is not part of this item: its printed constants do not follow from (47).
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Lemma 5.1 (i), p. 28

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem lemma_5_1_i {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ)
    (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) (hC : MLLangevin.ConvexA1.CondC b α) (hα : 0 < α) (hαL : α ≤ L)
    (hσ : 0 < σ) (xs : SDEState d) :
    (∀ γ : ℝ, 0 < γ → γ ≤ α / (2 * L ^ 2) → ∀ (t : ℝ≥0) (x : SDEState d),
      eLpNorm (fun ω => eulerCont b σ γ x W t ω - xs) 2 P ^ 2 ≤
        ENNReal.ofReal (‖x - xs‖ ^ 2 * Real.exp (-(α / 2) * t)
          + ‖b xs‖ ^ 2 * (1 / L ^ 2 + 2 / α ^ 2) + 2 * σ ^ 2 * d / α)) ∧
    (∀ γ : ℝ, 0 < γ → γ ≤ α / (2 * L ^ 2) →
      ∃! πγ : Measure (SDEState d), IsProbabilityMeasure πγ ∧ IsInvChain b σ γ πγ) := by sorry

end MLLangevin.ConvexA2
