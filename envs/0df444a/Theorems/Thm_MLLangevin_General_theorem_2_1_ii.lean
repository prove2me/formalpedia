-- Prove2me | Theorems.Thm_MLLangevin_General_theorem_2_1_ii
-- name    : MLLangevin.General.theorem_2_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:20.621768+00:00
-- url     : https://prove2.me/theorems/5e8c1662-2664-4478-b157-42f5051044e4
-- title:
--   Theorem 2.1 (ii), pp. 7–8 — with (8), (39)–(40): ‖𝒴 − π(f)‖₂ ≤ 𝔆₁[f]₁ε, 𝔆₁ universal, at cost 𝔠_𝔞γ₀⁻¹𝔱ε⁻² (𝔞 > 1) or 𝔠_𝔞γ₀⁻¹𝔱ε⁻²R_ε³ (𝔞 = 1)
-- statement:
--   There is a universal constant $\mathfrak C_1$ such that the following holds. Let $B^{(0)},B^{(1)},\dots$ be independent standard $d$-dimensional Brownian motions, $b:\mathbb R^d\to\mathbb R^d$ and $\sigma:\mathbb R^d\to\mathbb M_{d,d}$ Lipschitz, $f:\mathbb R^d\to\mathbb R$ Lipschitz, $\pi$ a probability measure and $(\pi^\gamma)_{\gamma\in(0,\eta_0]}$ probability measures, $f$ integrable for each of them. Assume $(\mathbf H_1)$–$(\mathbf H_4)$ (with $(\mathbf H_1)$, $(\mathbf H_2)$, $(\mathbf H_4)$ for every level's Brownian motion) with $\alpha\in(0,1]$, $\mathfrak a\in[1,2]$, $x_0\in\mathbb R^d$ and $\eta_0\in(0,1/2]$.
--
--   Let $\gamma_0\in(0,\eta_0]$, $r_0\ge1\vee(c_3\gamma_0^\delta)$, $\mathfrak t>0$ with $\mathfrak t\ge\mathfrak t_0$, and $\varepsilon\in(0,1)$. Set, as in (8),
--   $$\gamma_r=\gamma_02^{-r},\qquad R_\varepsilon=\Big\lceil\frac1\delta\log_2(r_0\varepsilon^{-1})\Big\rceil,\qquad T_r=\begin{cases}\mathfrak t\varepsilon^{-2}2^{-\frac{1+\mathfrak a}2r}&\mathfrak a>1,\\ \mathfrak t\varepsilon^{-2}R_\varepsilon^22^{-r}&\mathfrak a=1,\end{cases}$$
--   and let $\tau\in[\tau_1|\log\varepsilon|+\tau_2,\tfrac12T_{R_\varepsilon}]$, with $\mathfrak t_0,\tau_1,\tau_2$ given by (39)–(40). Then the multilevel occupation measure $\mathcal Y=\mathcal Y(R_\varepsilon,(\gamma_r)_r,\tau,(T_r)_r,f)$ satisfies
--   $$\|\mathcal Y-\pi(f)\|_2\le\mathfrak C_1[f]_1\varepsilon,\qquad \mathcal C(\mathcal Y)\le\mathfrak c_{\mathfrak a}\gamma_0^{-1}\mathfrak t\begin{cases}\varepsilon^{-2}&\mathfrak a>1,\\ \varepsilon^{-2}R_\varepsilon^3&\mathfrak a=1,\end{cases}$$
--   with $\mathfrak c_{\mathfrak a}=1+\frac32(2^{\frac{\mathfrak a-1}2}-1)^{-1}$ if $\mathfrak a>1$ and $\mathfrak c_{\mathfrak a}=\frac52$ if $\mathfrak a=1$.
--
--   This is the paper's general complexity result: an $\varepsilon$-approximation of $\pi(f)$ in $L^2$ at cost of order $\varepsilon^{-2}$, or $\varepsilon^{-2}|\log\varepsilon|^3$ in the borderline case $\mathfrak a=1$, with explicit parameters and a constant that does not depend on the dimension, the diffusion or $f$.
--
--   **Formalization Note.** $\mathfrak C_1$ is quantified before every datum ("$\mathfrak C_1\lesssim_{uc}1$"). The page restricts to $\varepsilon\in(0,\varepsilon_0)$ with $\varepsilon_0=\max\{\varepsilon\in(0,1]:\tau_1|\log\varepsilon|+\tau_2\le\frac12T_{R_\varepsilon}\}$, whose only role is to make the interval of admissible $\tau$ nonempty (p. 8); the Lean statement quantifies over every $\varepsilon\in(0,1)$ and every $\tau$ in that interval, which is the same claim wherever the page makes one. $\pi$ is any probability measure satisfying $(\mathbf H_3)$, in particular the invariant distribution of the SDE $dX_t=b(X_t)dt+\sigma(X_t)dB_t$; $\pi^\gamma$ is any family satisfying $(\mathbf H_1)$, in particular the invariant distributions of the Euler schemes. The SDE itself is not formalized. $(\mathbf H_4)$ is used at grid times only (a weaker assumption than the page's). The cost $\mathcal C(\mathcal Y)$ is the formula of p. 6.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Theorem 2.1 (ii) with (8)–(10), pp. 7–8; (39)–(40) of Proposition 4.1 (ii), p. 26

import Mathlib
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem theorem_2_1_ii :
    ∃ C₁ : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℕ → ℝ≥0 → Ω → Rd d), (∀ r, EthierKurtz.IsStandardBrownian P (B r)) →
      iIndepFun (fun r ω => fun t => B r t ω) P →
      ∀ (b : Rd d → Rd d) (σ : Rd d → (Rd d →L[ℝ] Rd d)),
      (∃ K, LipschitzWith K b) → (∃ K, LipschitzWith K σ) →
      ∀ (f : Rd d → ℝ), (∃ K, LipschitzWith K f) →
      ∀ (π : Measure (Rd d)) [IsProbabilityMeasure π] (πγ : ℝ → Measure (Rd d))
        (α 𝔞 δ η₀ : ℝ) (x₀ : Rd d) (c₁ : Rd d → ℝ) (c₂ c₃ c₄ : ℝ),
      (∀ γ ∈ Set.Ioc (0 : ℝ) η₀, IsProbabilityMeasure (πγ γ)) →
      Integrable f π → (∀ γ ∈ Set.Ioc (0 : ℝ) η₀, Integrable f (πγ γ)) →
      0 < α → α ≤ 1 → 1 ≤ 𝔞 → 𝔞 ≤ 2 → 0 < η₀ → η₀ ≤ 1 / 2 →
      (∀ r, H1 P b σ (B r) f πγ α η₀ c₁) → (∀ r, H2 P b σ (B r) x₀ η₀ 𝔞 c₂) →
      H3 f π πγ η₀ 𝔞 δ c₃ → (∀ r, H4 P b σ (B r) x₀ η₀ c₁ c₄) →
      ∀ (γ₀ r₀ 𝔱 ε τ : ℝ), 0 < γ₀ → γ₀ ≤ η₀ → max 1 (c₃ * γ₀ ^ δ) ≤ r₀ → 0 < 𝔱 →
      t0 𝔞 α c₂ c₄ γ₀ ≤ 𝔱 → 0 < ε → ε < 1 →
      tau1 𝔞 α δ * |Real.log ε| + tau2 𝔞 α δ r₀ c₄ ≤ τ →
      τ ≤ Tsched 𝔞 𝔱 ε (Reps r₀ δ ε) (Reps r₀ δ ε) / 2 →
      eLpNorm (fun ω => estimator b σ x₀ γ₀ (Reps r₀ δ ε) τ (Tsched 𝔞 𝔱 ε (Reps r₀ δ ε)) B f ω
            - ∫ y, f y ∂π) 2 P
          ≤ ENNReal.ofReal (C₁ * lipConst f * ε) ∧
        cost (Reps r₀ δ ε) γ₀ (Tsched 𝔞 𝔱 ε (Reps r₀ δ ε))
          ≤ ca 𝔞 * γ₀⁻¹ * 𝔱 * (if 1 < 𝔞 then ε⁻¹ ^ 2 else ε⁻¹ ^ 2 * (Reps r₀ δ ε : ℝ) ^ 3) := by sorry

end MLLangevin.General
