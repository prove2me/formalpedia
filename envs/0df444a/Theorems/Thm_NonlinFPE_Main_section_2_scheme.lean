-- Prove2me | Theorems.Thm_NonlinFPE_Main_section_2_scheme
-- name    : NonlinFPE.Main.section_2_scheme
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:46.842816+00:00
-- url     : https://prove2.me/theorems/237f9f0b-d994-482d-848a-4c54c8a81bd5
-- title:
--   §2, pp. 5–6 — a weakly continuous probability solution (μ_t) of the linear FPE (1.2) with bounded coefficients is the law of a weak solution of (2.2)
-- statement:
--   Let $\bar a_{ij}(t,x)$, $\bar b_i(t,x)$ be jointly measurable and bounded on $[0,\infty)\times\mathbb R^d$ (the coefficients $a_{ij}(t,x,\mu_t)$, $b_i(t,x,\mu_t)$ of §2 frozen along a curve $(\mu_t)$), and let $\bar\sigma(t,x)$ be a measurable $d\times d$ matrix with $\bar\sigma\bar\sigma^T = \bar a$. Let $(\mu_t)_{t\ge0}$ be a weakly continuous curve of probability measures on $\mathbb R^d$ solving (1.2): for every $\varphi \in C_0^2(\mathbb R^d)$ and $t \ge 0$,
--   $$\int\varphi\,d\mu_t = \int\varphi\,d\mu_0 + \int_0^t\!\!\int L_s\varphi(x)\,\mu_s(dx)\,ds, \qquad L_s = \frac12\sum_{i,j=1}^d \bar a_{ij}(s,x)\frac{\partial^2}{\partial x_i\partial x_j} + \sum_{i=1}^d \bar b_i(s,x)\frac{\partial}{\partial x_i}. \tag{2.1}$$
--   Then for every $T > 0$ there are a probability space $(\Omega,\mathcal F,Q)$ with a filtration, a $d$-dimensional Brownian motion $W$ and a continuous adapted process $X$ solving
--   $$dX(t) = \bar b(t,X(t))\,dt + \bar\sigma(t,X(t))\,dW(t), \qquad 0 \le t \le T, \tag{2.2}$$
--   with $Q\circ X(0)^{-1} = \mu_0$ and
--   $$Q\circ X(t)^{-1} = \mu_t, \qquad t \in [0,T]. \tag{2.3}$$
--
--   This is the superposition principle plus a martingale-problem-to-SDE step; it turns a solution of the nonlinear FPE into a probabilistic representation.
--
--   **Formalization Note** Boundedness of $\bar a$, $\bar b$ replaces the integrability Hypothesis 2.1 (ii) (a disclosed strengthening of the hypotheses): the published `EthierKurtz.IsWeakSDESolution` asks for pathwise integrability for *every* $\omega$, which (ii) gives only almost surely; the bounded case is the one Theorem 4.1 uses. Any measurable $\bar\sigma$ with $\bar\sigma\bar\sigma^T = \bar a$ is allowed (the page takes $\bar a^{1/2}$, one such choice). The SDE is posed on $[0,T]$ through coefficients switched off after $T$, so (2.3) is asserted for $t \le T$. Hypothesis 2.1 (iii) is continuity into the space of probability measures with the weak topology; $C_0^2$ test functions are $C^2$ with compact support.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §2, pp. 5–6, Hypothesis 2.1, (2.1)–(2.3), with (1.2)–(1.3), p. 2

import Mathlib
import Definitions.Def_EthierKurtz_IsWeakSDESolution
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive
import Definitions.Def_NonlinFPE_Main_SDE

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz HunterPDE.Shared

/-- §2, pp. 5–6 (general scheme), for coefficients frozen along the curve `(μ_t)`:
`ā(t,x) = a(t,x,μ_t)`, `b̄(t,x) = b(t,x,μ_t)`, jointly measurable and bounded. If `(μ_t)` is a weakly
continuous curve of probability measures solving (1.2) with the Kolmogorov operator (2.1)
`L = ½ ∑ᵢⱼ āᵢⱼ ∂ᵢⱼ + ∑ᵢ b̄ᵢ ∂ᵢ`, and `σ̄` is measurable with `σ̄σ̄ᵀ = ā`, then for every `T > 0` there
is a weak solution of (2.2) `dX = b̄(t,X)dt + σ̄(t,X)dW` (coefficients switched off after `T`) with
`X(0) ∼ μ₀` and marginals (2.3) `Law(X(t)) = μ_t`, `t ∈ [0, T]`. -/
theorem section_2_scheme {d : ℕ} (abar : ℝ≥0 → SDEState d → Fin d → Fin d → ℝ)
    (bbar : ℝ≥0 → SDEState d → Fin d → ℝ) (σbar : ℝ≥0 → SDEState d → Fin d → Fin d → ℝ)
    (μ : ℝ≥0 → ProbabilityMeasure (SDEState d))
    (ha_meas : ∀ i j, Measurable (fun p : ℝ≥0 × SDEState d => abar p.1 p.2 i j))
    (hb_meas : ∀ i, Measurable (fun p : ℝ≥0 × SDEState d => bbar p.1 p.2 i))
    (ha_bdd : ∃ M : ℝ, ∀ t x i j, |abar t x i j| ≤ M)
    (hb_bdd : ∃ M : ℝ, ∀ t x i, |bbar t x i| ≤ M)
    (hσ_meas : ∀ i j, Measurable (fun p : ℝ≥0 × SDEState d => σbar p.1 p.2 i j))
    (hσ : ∀ t x i j, ∑ k, σbar t x i k * σbar t x j k = abar t x i j)
    (hμ_cont : Continuous μ)
    (hFPE : ∀ φ : SDEState d → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t : ℝ≥0,
      ∫ x, φ x ∂(μ t : Measure (SDEState d)) =
        ∫ x, φ x ∂(μ 0 : Measure (SDEState d)) +
          ∫ s in (0 : ℝ)..(t : ℝ), ∫ x,
            ((1 / 2 : ℝ) * ∑ i, ∑ j, abar s.toNNReal x i j * pd2 φ i j x +
              ∑ i, bbar s.toNNReal x i * partialDeriv φ i x) ∂(μ s.toNNReal : Measure (SDEState d)))
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
      (W X : ℝ≥0 → Ω → SDEState d),
      IsProbabilityMeasure P ∧
      IsWeakSDESolution P ℱ (cutDiff T σbar) (cutDrift T bbar) (μ 0 : Measure (SDEState d)) W X ∧
      ∀ t : ℝ≥0, t ≤ T → P.map (X t) = (μ t : Measure (SDEState d)) := by sorry

end NonlinFPE.Main
