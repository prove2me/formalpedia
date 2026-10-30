-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_proof_3_1_derivative_continuity
-- name    : LyapDiffMC.RandomHorizon.proof_3_1_derivative_continuity
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T11:22:24.203503+00:00
-- url     : https://prove2.me/theorems/a94b26c3-c0ae-488e-b1c0-d1890b7a6e5d
-- title:
--   Proof of Theorem 3.1, p. 13 — under (3.14) and (3.12′), the derivative u*′(·, x) is continuous on [θ₀ − ε, θ₀ + ε]
-- statement:
--   Throughout, $S$ is a measurable state space, $(P(\theta):\theta\in\Lambda)$ a family of Markov transition kernels on $S$ indexed by an open interval $\Lambda=(a,b)$, $f, g : S\to\mathbb R$ measurable, and $\emptyset\neq C\subseteq S$ measurable. The non-negative kernel $K(\theta,x,dy)=e^{g(x)}P(\theta,x,dy)$ restricted to $y\in C$ is $K(\theta)$, its powers are $K^n(\theta)$ ($K^0(x,dy)=\delta_x(dy)$), $G(\theta,x,dy)=\sum_{n\ge0}K^n(\theta,x,dy)$ (possibly an infinite measure), $\tilde f(\theta,x)=f(x)+\int_{C^c}K(\theta,x,dy)f(y)$, and $u^*(\theta,x)=\sum_{n\ge0}(K^n(\theta)\tilde f(\theta))(x)=\int \tilde f(\theta,y)\,G(\theta,x,dy)$. Write $K=K(\theta_0)$ and $G=G(\theta_0)$.
--
--   Let $k(\theta,x,y)$ be a measurable density with $K(\theta,x,dy)=k(\theta,x,y)K(x,dy)$ for $\theta\in\Lambda$, $x\in C$ and all $y$ (A1 for $y\in C$, A3 for $y\in C^c$), such that $k(\cdot,x,y)$ is continuously differentiable on $[\theta_0-\varepsilon,\theta_0+\varepsilon]\subseteq\Lambda$ with derivative $k'(\cdot,x,y)$ (A2, A3). Put $\omega_\varepsilon(x,y)=\sup_{|\theta-\theta_0|<\varepsilon}|k'(\theta,x,y)|$ (written $\tilde\omega_\varepsilon$ when $y\in C^c$), $k'(x,y)=k'(\theta_0,x,y)$, and $\tilde r_\varepsilon(x)=\int_{C^c}\tilde\omega_\varepsilon(x,y)|f(y)|K(x,dy)$, assumed finite for $x\in C$ (A3). Assume $f$ is integrable on $C^c$ against $K(\theta,x,\cdot)$ for $|\theta-\theta_0|<\varepsilon$, $x\in C$, so that $\tilde f(\theta,x)$ is a real number.
--
--   Let $v_0,v_1$ be finite non-negative measurable functions on $C$ with
--   $$(K(\theta)v_0)(x)\le v_0(x)-|\tilde f(\theta,x)|\quad(x\in C,\ |\theta-\theta_0|<\varepsilon),\tag{3.11}$$
--   $$(Kv_1)(x)\le v_1(x)-\int_C\omega_\varepsilon(x,y)v_0(y)K(x,dy)-\tilde r_\varepsilon(x)\quad(x\in C).\tag{3.12}$$
--
--   Assume in addition
--   $$\int_C\omega_\varepsilon(x,y)v_1(y)K(x,dy)<\infty\quad(x\in C)\tag{3.14}$$
--   and, for $\theta\in[\theta_0-\varepsilon,\theta_0+\varepsilon]$ and $x\in C$,
--   $$(K(\theta)v_1)(x)\le v_1(x)-\int_C\omega_\varepsilon(x,y)v_0(y)K(\theta,x,dy)-\int_{C^c}\tilde\omega_\varepsilon(x,y)|f(y)|K(\theta,x,dy).\tag{3.12$'$}$$
--   Let $u^{*\prime}(\theta,x)$ denote the derivative of $u^*(\cdot,x)$ within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$ (one-sided at the endpoints). Then for every $x\in C$,
--   $$\theta\mapsto u^{*\prime}(\theta,x)\ \text{ is continuous on }[\theta_0-\varepsilon,\theta_0+\varepsilon],$$
--   i.e. $u^{*\prime}(\theta+h,x)-u^{*\prime}(\theta,x)\to0$ as $h\to0$ with $\theta,\theta+h\in[\theta_0-\varepsilon,\theta_0+\varepsilon]$.
--
--   This is the final step of the proof of Theorem 3.1 (II) (p. 13, "Turning to the continuity of $u^{*\prime}(\cdot,x)$ ... shows that $u^{*\prime}(\theta+h)-u^{*\prime}(\theta)\to0$"). Together with the differentiated equation `proof_3_1_derivative_equation` (which provides the derivative within the interval at every point), it gives clause (II) of Theorem 3.1: $u^*(\cdot,x)$ is continuously differentiable on $[\theta_0-\varepsilon,\theta_0+\varepsilon]$, with one-sided derivatives at the endpoints.
--
--   **Formalization Note** The hypotheses are exactly those of `LyapDiffMC.RandomHorizon.proof_3_1_derivative_equation` (the hypotheses of Theorem 3.1 together with (3.14) and (3.12$'$)). The derivative is Mathlib's `derivWithin` on `Set.Icc (θ₀ - ε) (θ₀ + ε)`; continuity is `ContinuousOn` on the closed interval. The statement is implied by clause (II) of `theorem_3_1` (a $C^1$ function on a closed interval has a continuous derivative within it).
-- source:
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 13, proof of Theorem 3.1 ("Turning to the continuity of u*′(·, x) ... shows that u*′(θ + h) − u*′(θ) → 0 for θ ∈ [θ0 − ε, θ0 + ε]")

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- Proof of Theorem 3.1, continuity of the derivative (p. 13). Under the hypotheses of
Theorem 3.1 together with (3.14) and (3.12′), for every `x ∈ C` the derivative
`u*′(θ, x)` of `u*(·, x)` within `[θ₀ - ε, θ₀ + ε]` depends continuously on
`θ ∈ [θ₀ - ε, θ₀ + ε]`. -/
theorem proof_3_1_derivative_continuity {S : Type*} [MeasurableSpace S] (M : Setting S)
    (a b θ₀ ε : ℝ) (hθ₀ : θ₀ ∈ Set.Ioo a b) (hε : 0 < ε)
    (hεΛ : Set.Icc (θ₀ - ε) (θ₀ + ε) ⊆ Set.Ioo a b)
    (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ)))
    -- A1 and A3: K(θ, x, dy) = k(θ, x, y) K(θ₀, x, dy) for x ∈ C, y ∈ C and y ∈ Cᶜ
    (hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y)))
    (hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y)
    -- A2 and A3: k(·, x, y) is continuously differentiable on [θ₀ - ε, θ₀ + ε]
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    -- A3: r̃_ε(x) < ∞
    (hA3 : ∀ x ∈ M.C, rtilde M k θ₀ ε x < ⊤)
    -- f̃(θ, x) in (3.11) is a real number
    (hf_int : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      IntegrableOn M.f M.Cᶜ (discKernel M θ x))
    (v₀ v₁ : S → ℝ) (hv₀ : Measurable v₀) (hv₁ : Measurable v₁)
    (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x) (hv₁_nn : ∀ x ∈ M.C, 0 ≤ v₁ x)
    -- (3.11)
    (h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x))
    -- (3.12)
    (h312 : ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x)
        + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ₀ x)
        + rtilde M k θ₀ ε x ≤ ENNReal.ofReal (v₁ x))
    -- (3.14)
    (h314 : ∀ x ∈ M.C,
      ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x) < ⊤)
    -- (3.12′)
    (h312' : ∀ θ ∈ Set.Icc (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ x)
        + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ x)
        + ∫⁻ y in M.Cᶜ, omega k θ₀ ε x y * ‖M.f y‖ₑ ∂(discKernel M θ x)
        ≤ ENNReal.ofReal (v₁ x)) :
    ∀ x ∈ M.C, ContinuousOn
      (fun θ => derivWithin (fun t => uStar M t x) (Set.Icc (θ₀ - ε) (θ₀ + ε)) θ)
      (Set.Icc (θ₀ - ε) (θ₀ + ε)) := by sorry

end LyapDiffMC.RandomHorizon
