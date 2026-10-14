-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_theorem_2_3
-- name    : MLLangevin.ConvexA2.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:22.032066+00:00
-- url     : https://prove2.me/theorems/dd27a676-b138-447f-bb34-85fac93681ba
-- title:
--   Theorem 2.3, p. 12 — under (C_α) and 𝒞² drift, ‖𝒴 − π(f)‖₂ ≤ 𝔆₁[f]₁ε with 𝔆₁ universal at cost ((½+√2)/(√2−1))Υ₂²log(γ₀⁻¹)ε⁻²/(γ₀α)
-- statement:
--   There is a universal constant $\mathfrak C_1$ such that the following holds. Assume $(\mathbf C_\alpha)$ with $\alpha\in(0,L\wedge1]$, that $b$ is $L$-Lipschitz and $\mathcal C^2$ with bounded partial derivatives up to order 2, and $\sigma>0$. Let $B^{(0)},B^{(1)},\dots$ be independent standard $d$-dimensional Brownian motions, $X^x$ the solution of $X^x_t=x+\int_0^tb(X^x_s)ds+\sigma B^{(0)}_t$ for each $x$, and $\pi$ a probability measure invariant for this diffusion. Let $f:\mathbb R^d\to\mathbb R$ be Lipschitz and $\pi$-integrable, $x_0\in\mathbb R^d$, $\gamma_0\in(0,\frac{\alpha}{2L^2}\wedge\frac12]$, and let $\Upsilon_2$ be defined by (19). Let $\varepsilon\in(0,1)$ satisfy
--   $$\sqrt2\log(\Upsilon_2\varepsilon^{-2})\le\log(\gamma_0^{-1})(\Upsilon_2\varepsilon^{-1})^{1/2},$$
--   and set
--   $$r_0=\Upsilon_2,\quad R_\varepsilon=\lceil\log_2(r_0\varepsilon^{-1})\rceil,\quad T_r=\frac{\Upsilon_2^2\log(\gamma_0^{-1})}{\alpha}\varepsilon^{-2}2^{-\frac32r}\ (0\le r\le R_\varepsilon),\quad\tau=\alpha^{-1}|\log\varepsilon|+(2\alpha)^{-1}\log\Upsilon_2,$$
--   and $\gamma_r=\gamma_02^{-r}$. Then the multilevel occupation measure $\mathcal Y$ of (7) with these parameters satisfies
--   $$\big\|\mathcal Y(R_\varepsilon,(\gamma_r)_r,\tau,(T_r)_r,f)-\pi(f)\big\|_2\le\mathfrak C_1[f]_1\varepsilon \tag{9}$$
--   and
--   $$\mathcal C(\mathcal Y)\le\frac{\frac12+\sqrt2}{\sqrt2-1}\,\frac{\Upsilon_2^2\log(\gamma_0^{-1})}{\gamma_0\alpha}\,\varepsilon^{-2}. \tag{21}$$
--
--   The cost is of order $\varepsilon^{-2}$, the order of a Monte Carlo method without bias, with no logarithmic factor in $\varepsilon$.
--
--   **Formalization Note** The paper defines $\varepsilon_0$ as the maximum of the set of $\varepsilon\in(0,1]$ satisfying the displayed inequality and states the result for $\varepsilon\in(0,\varepsilon_0)$; that set need not be an interval, and the statement here is made for every $\varepsilon\in(0,1)$ in the set. The universal constant $\mathfrak C_1$ is quantified before every datum. $\|\cdot\|_2$ is the $L^2(\mathbb P)$ norm in $[0,\infty]$. The diffusion is driven by $B^{(0)}$; invariance is a property of the law. $f\in L^1(\pi)$ is assumed so that $\pi(f)$ is a number. The cost is the formula of p. 6, used for every $T_r$.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Theorem 2.3, (9) and (21), p. 12 (with (7), p. 6, and (19), p. 11)

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem theorem_2_3 :
    ∃ C₁ : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℕ → ℝ≥0 → Ω → SDEState d), (∀ r, IsStandardBrownian P (B r)) →
      iIndepFun (fun r ω => fun t => B r t ω) P →
      ∀ (b : SDEState d → SDEState d) (L α σ : ℝ),
      (∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) → MLLangevin.ConvexA1.CondC b α → 0 < α → α ≤ min L 1 → C2Bounded b →
      0 < σ →
      ∀ (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d), (∀ x, IsAddSolution b σ (B 0) x (Xsol x)) →
      ∀ (π : Measure (SDEState d)), IsProbabilityMeasure π → IsInvDiffusion P Xsol π →
      ∀ f : SDEState d → ℝ, (∃ K, LipschitzWith K f) → Integrable f π →
      ∀ (x₀ : SDEState d) (γ₀ ε : ℝ), 0 < γ₀ → γ₀ ≤ min (α / (2 * L ^ 2)) (1 / 2) →
      0 < ε → ε < 1 →
      Real.sqrt 2 * Real.log (Real.sqrt (Upsilon2Sq b σ α L x₀) * ε⁻¹ ^ 2)
        ≤ Real.log γ₀⁻¹ * Real.sqrt (Real.sqrt (Upsilon2Sq b σ α L x₀) * ε⁻¹) →
      let R : ℕ := ⌈Real.logb 2 (Real.sqrt (Upsilon2Sq b σ α L x₀) / ε)⌉₊
      let T : ℕ → ℝ := fun r =>
        Upsilon2Sq b σ α L x₀ * Real.log γ₀⁻¹ / α * ε⁻¹ ^ 2 * (2 : ℝ) ^ (-(3 / 2) * (r : ℝ))
      let τ : ℝ := α⁻¹ * |Real.log ε| + (2 * α)⁻¹ * Real.log (Real.sqrt (Upsilon2Sq b σ α L x₀))
      eLpNorm (fun ω => estimator b σ x₀ γ₀ R τ T B f ω - ∫ x, f x ∂π) 2 P
          ≤ ENNReal.ofReal (C₁ * MLLangevin.ConvexA1.lipConst f * ε) ∧
        cost R γ₀ T ≤ (1 / 2 + Real.sqrt 2) / (Real.sqrt 2 - 1)
          * (Upsilon2Sq b σ α L x₀ * Real.log γ₀⁻¹ / (γ₀ * α)) * ε⁻¹ ^ 2 := by sorry

end MLLangevin.ConvexA2
