-- Prove2me | Theorems.Thm_GraphLQGame_DenseApprox_lemma_7_2
-- name    : GraphLQGame.DenseApprox.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:25:44.19488+00:00
-- url     : https://prove2.me/theorems/6e40c737-1004-4e4f-9ebe-53d15dbf9dbb
-- title:
--   Lemma 7.2 — the mean-field control $\alpha^{\mathrm{MF}}$ solves the one-player LQ problem against every progressive control
-- statement:
--   Let $T,\sigma,c>0$ and $\alpha^{\mathrm{MF}}(t,x)=-cx/(1+c(T-t))$. Let $(\Omega,\mathcal F,\mathbb F,\mathbb P)$ be a filtered probability space supporting an $\mathbb F$-Brownian motion $W$ and an $\mathbb F$-progressively measurable real process $(\beta(t))_{t\in[0,T]}$ with $\mathbb E\int_0^T\beta(t)^2dt<\infty$. Let $X$ be the solution of
--   $$dX(t)=\alpha^{\mathrm{MF}}(t,X(t))\,dt+\sigma\,dW(t),\qquad X(0)=0,$$
--   and $Y(t)=\int_0^t\beta(s)\,ds+\sigma W(t)$. Then
--   $$\frac12\mathbb E\Big[\int_0^T|\alpha^{\mathrm{MF}}(t,X(t))|^2dt+c|X(T)|^2\Big]\le\frac12\mathbb E\Big[\int_0^T|\beta(t)|^2dt+c|Y(T)|^2\Big].$$
--
--   So $\alpha^{\mathrm{MF}}$ is optimal for the control problem whose value is the cost of an isolated player; it is the control obtained from the corresponding mean field game, and the building block of every step of the proof of Theorem 2.11.
--
--   **Formalization Note** $X$ ranges over every continuous $\mathbb F$-adapted process satisfying the integral equation almost surely on $[0,T]$; this equation is a linear ODE driven by $W$, so this is the paper's unique strong solution. $\beta$ is progressively measurable on all of $\mathbb R_{\ge0}$ (Mathlib's `IsStronglyProgressive`); a process progressive on $[0,T]$ extends to one, and only its values on $[0,T]$ enter. $Y(T)$ is written pathwise. Both sides are $[0,\infty]$-valued lower Lebesgue integrals. $T,\sigma,c>0$ are the standing assumptions of §2.1.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Lemma 7.2 with (7.4), pp. 39–40

import Mathlib
import Definitions.Def_GraphLQGame_DenseApprox_MeanField
import Definitions.Def_GraphLQGame_DenseApprox_FBrownian

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

/-- **Lemma 7.2** (Lacker–Soret, arXiv:2005.14102v2, pp. 39–40): the one-player linear-quadratic
control problem solved by the mean-field control (7.4).

Let `(Ω, 𝓕, 𝔽, P)` be a filtered probability space with an `𝔽`-Brownian motion `W` and an
`𝔽`-progressively measurable real process `β` with `E ∫₀ᵀ β(t)² dt < ∞`. Let `X` solve
`dX(t) = α^MF(t, X(t)) dt + σ dW(t)`, `X(0) = 0`, and let `Y(t) = ∫₀ᵗ β(s) ds + σ W(t)`. Then
`½ E[∫₀ᵀ |α^MF(t, X(t))|² dt + c |X(T)|²] ≤ ½ E[∫₀ᵀ |β(t)|² dt + c |Y(T)|²]`.

Formalization Note: time is real, `W` and `β` are indexed by `ℝ≥0` and read at `t.toNNReal`.
`β` is progressively measurable on all of `ℝ≥0` (Mathlib's `IsStronglyProgressive`); a process
progressive on `[0, T]` extends to one (e.g. by `0` after `T`) and only values on `[0, T]` enter.
"The unique strong solution" `X` is quantified as every continuous `𝔽`-adapted process satisfying
the integral equation almost surely on `[0, T]`; the equation is a linear ODE driven by `W`, so
this is the same process. Only `Y(T)` enters the conclusion, written pathwise as
`∫₀ᵀ β(s) ds + σ W(T)`. Both sides are `ℝ≥0∞`-valued lower Lebesgue integrals. The standing
assumptions `T > 0`, `σ > 0`, `c > 0` of §2.1 are hypotheses. -/
theorem lemma_7_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) {T σ c : ℝ} (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c)
    (W : ℝ≥0 → Ω → ℝ) (hW : IsFBrownianReal 𝓕 P W)
    (β : ℝ≥0 → Ω → ℝ) (hβ : IsStronglyProgressive 𝓕 β)
    (hβL2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((β t.toNNReal ω) ^ 2)) ∂P < ⊤)
    (X : ℝ → Ω → ℝ) (hXcont : ∀ ω, ContinuousOn (fun t => X t ω) (Set.Icc 0 T))
    (hXadapt : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[𝓕 t.toNNReal] (X t))
    (hX : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      X t ω = (∫ s in (0 : ℝ)..t, alphaMF c T s (X s ω)) + σ * W t.toNNReal ω) :
    ∫⁻ ω, ENNReal.ofReal (1 / 2) *
        ((∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((alphaMF c T t (X t ω)) ^ 2)) +
          ENNReal.ofReal (c * (X T ω) ^ 2)) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (1 / 2) *
        ((∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((β t.toNNReal ω) ^ 2)) +
          ENNReal.ofReal
            (c * ((∫ s in (0 : ℝ)..T, β s.toNNReal ω) + σ * W T.toNNReal ω) ^ 2)) ∂P := by sorry

end GraphLQGame.DenseApprox
