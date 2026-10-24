-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_eq_3_24
-- name    : LyapDiffMC.RandomHorizon.eq_3_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:41.600043+00:00
-- url     : https://prove2.me/theorems/10d16265-4f19-4b26-903a-319a8a2e0123
-- title:
--   (3.24), p. 13 — ∫_C G(x, dy)(∫_C ω_ε(y, z)v₀(z)K(y, dz) + ∫_{Cᶜ} ω̃_ε(y, z)|f(z)|K(y, dz)) < ∞
-- statement:
--   Throughout, $S$ is a measurable state space, $(P(\theta):\theta\in\Lambda)$ a family of Markov transition kernels on $S$ indexed by an open interval $\Lambda=(a,b)$, $f, g : S\to\mathbb R$ measurable, and $\emptyset\neq C\subseteq S$ measurable. The non-negative kernel $K(\theta,x,dy)=e^{g(x)}P(\theta,x,dy)$ restricted to $y\in C$ is $K(\theta)$, its powers are $K^n(\theta)$ ($K^0(x,dy)=\delta_x(dy)$), $G(\theta,x,dy)=\sum_{n\ge0}K^n(\theta,x,dy)$ (possibly an infinite measure), $\tilde f(\theta,x)=f(x)+\int_{C^c}K(\theta,x,dy)f(y)$, and $u^*(\theta,x)=\sum_{n\ge0}(K^n(\theta)\tilde f(\theta))(x)=\int \tilde f(\theta,y)\,G(\theta,x,dy)$. Write $K=K(\theta_0)$ and $G=G(\theta_0)$.
--
--   Let $\varepsilon>0$, and let $k(\theta,x,y)$ be measurable in $(x,y)$ for $\theta\in[\theta_0-\varepsilon,\theta_0+\varepsilon]$, with $k(\cdot,x,y)$ continuously differentiable on $[\theta_0-\varepsilon,\theta_0+\varepsilon]$ for $x\in C$ and every $y$, with derivative $k'$. Put $\omega_\varepsilon(x,y)=\sup_{|\theta-\theta_0|<\varepsilon}|k'(\theta,x,y)|$ ($\tilde\omega_\varepsilon$ for $y\in C^c$) and $\tilde r_\varepsilon(x)=\int_{C^c}\tilde\omega_\varepsilon(x,y)|f(y)|K(x,dy)$. Let $v_0,v_1$ be finite, non-negative, measurable functions on $C$ satisfying the Lyapunov bound
--   $$(Kv_1)(x)\le v_1(x)-\int_C\omega_\varepsilon(x,y)v_0(y)K(x,dy)-\tilde r_\varepsilon(x)\quad(x\in C).\tag{3.12}$$
--   Then for every $x\in C$,
--   $$\int_C G(x,dy)\Big(\int_C\omega_\varepsilon(y,z)v_0(z)K(y,dz)+\int_{C^c}\tilde\omega_\varepsilon(y,z)|f(z)|K(y,dz)\Big)<\infty.\tag{3.24}$$
--
--   Together with the pointwise bounds (3.22)–(3.23), this is the integrable majorant for the dominated-convergence argument that proves differentiability of $u^*$ at $\theta_0$.
--
--   **Formalization Note** The Lyapunov inequalities are written additively in $[0,\infty]$ ($Kv+\dots\le v$), which is equivalent because $v_0,v_1$ are finite; $\omega_\varepsilon$ and $\tilde r_\varepsilon$ are $[0,\infty]$-valued. $k'$ is the derivative within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$, the ordinary derivative at interior points. One $\varepsilon$ serves A2, A3 and the Lyapunov conditions, as in the paper's proof. The family $P(\theta)$ is given for all real $\theta$; only $\theta\in\Lambda$ matters.
--
--   Differences from the source:
--   - generalization: the hypotheses of Theorem 3.1 are in force → only (3.12), A2 (k(·, x, y) C¹ on [θ₀ − ε, θ₀ + ε]), measurability of k(θ, ·, ·) on that interval and measurable v₀, v₁ ≥ 0 on C; reason: (3.24) follows from (3.12) and Proposition 3.1 (p. 13); A2 and the measurability of k make ω_ε measurable; under the theorem's hypotheses (with [θ₀ − ε, θ₀ + ε] ⊆ Λ) the statement specializes to the paper's
--   - encoding: separate ε's in A2, A3 and the theorem → one ε; reason: the proof takes the smallest of them (p. 12); shrinking ε keeps every hypothesis true, since ω_ε and r̃_ε only decrease
--   - encoding: (K v)(x) ≤ v(x) − (non-negative terms) in (3.11), (3.12), (3.12′) → (K v)(x) + (the terms) ≤ v(x) in ℝ≥0∞; reason: every term lies in [0, ∞] and v(x) is finite, so the two forms are equivalent
--   - encoding: v₀, v₁ finite-valued non-negative functions on C → v₀ v₁ : S → ℝ, non-negative on C; reason: values off C never enter the statement; same instances
--   - encoding: ω_ε(x, y) = sup{|k′(θ, x, y)| : |θ − θ₀| < ε}, ω̃_ε, r̃_ε → ℝ≥0∞-valued iSup (omega) and lintegral (rtilde); reason: the supremum may be +∞; a real supremum would return 0 on an unbounded set
--   - encoding: k′(θ, x, y), the derivative of k(·, x, y) on [θ₀ − ε, θ₀ + ε] → kder = derivWithin on Icc (θ₀ − ε) (θ₀ + ε); reason: the ordinary derivative at interior points (in particular at θ₀), the one-sided one at the endpoints, as A2's 'in [θ₀ − ε, θ₀ + ε]'
--   - encoding: measurability of v₀, v₁ left implicit → Measurable v₀, Measurable v₁; reason: (Kv)(x) is only defined for measurable v
-- source:
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 13, (3.24)

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- (3.24), p. 13. The Lyapunov bound (3.12) together with Proposition 3.1 gives
`∫_C G(x, dy)(∫_C ω_ε(y, z) v₀(z) K(y, dz) + ∫_{Cᶜ} ω̃_ε(y, z)|f(z)| K(y, dz)) < ∞` for `x ∈ C`. -/
theorem eq_3_24 {S : Type*} [MeasurableSpace S] (M : Setting S)
    (θ₀ ε : ℝ) (hε : 0 < ε) (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Icc (θ₀ - ε) (θ₀ + ε), Measurable (Function.uncurry (k θ)))
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    (v₀ v₁ : S → ℝ) (hv₀ : Measurable v₀) (hv₁ : Measurable v₁)
    (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x) (hv₁_nn : ∀ x ∈ M.C, 0 ≤ v₁ x)
    (h312 : ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x)
        + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ₀ x)
        + rtilde M k θ₀ ε x ≤ ENNReal.ofReal (v₁ x)) :
    ∀ x ∈ M.C,
      ∫⁻ y, (∫⁻ z in M.C, omega k θ₀ ε y z * ENNReal.ofReal (v₀ z) ∂(discKernel M θ₀ y)
          + ∫⁻ z in M.Cᶜ, omega k θ₀ ε y z * ‖M.f z‖ₑ ∂(discKernel M θ₀ y))
        ∂(greenMeasure M θ₀ x) < ⊤ := by sorry

end LyapDiffMC.RandomHorizon
