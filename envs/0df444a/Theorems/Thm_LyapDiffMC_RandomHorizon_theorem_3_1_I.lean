-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_theorem_3_1_I
-- name    : LyapDiffMC.RandomHorizon.theorem_3_1_I
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T11:22:26.457269+00:00
-- url     : https://prove2.me/theorems/19538b04-4485-449b-a7b6-c8246ec2acb3
-- title:
--   Theorem 3.1 (I), pp. 11–13 — Lyapunov conditions give differentiability of the random-horizon discounted expectation at θ₀, with derivative (3.25)
-- statement:
--   Throughout, $S$ is a measurable state space, $(P(\theta):\theta\in\Lambda)$ a family of Markov transition kernels on $S$ indexed by an open interval $\Lambda=(a,b)$, $f, g : S\to\mathbb R$ measurable, and $\emptyset\neq C\subseteq S$ measurable. The non-negative kernel $K(\theta,x,dy)=e^{g(x)}P(\theta,x,dy)$ restricted to $y\in C$ is $K(\theta)$, its powers are $K^n(\theta)$ ($K^0(x,dy)=\delta_x(dy)$), $G(\theta,x,dy)=\sum_{n\ge0}K^n(\theta,x,dy)$ (possibly an infinite measure), $\tilde f(\theta,x)=f(x)+\int_{C^c}K(\theta,x,dy)f(y)$, and $u^*(\theta,x)=\sum_{n\ge0}(K^n(\theta)\tilde f(\theta))(x)=\int \tilde f(\theta,y)\,G(\theta,x,dy)$. Write $K=K(\theta_0)$ and $G=G(\theta_0)$.
--
--   Let $k(\theta,x,y)$ be a measurable density with $K(\theta,x,dy)=k(\theta,x,y)K(x,dy)$ for $\theta\in\Lambda$, $x\in C$ and all $y$ (A1 for $y\in C$, A3 for $y\in C^c$), such that $k(\cdot,x,y)$ is continuously differentiable on $[\theta_0-\varepsilon,\theta_0+\varepsilon]\subseteq\Lambda$ with derivative $k'(\cdot,x,y)$ (A2, A3). Put $\omega_\varepsilon(x,y)=\sup_{|\theta-\theta_0|<\varepsilon}|k'(\theta,x,y)|$ (written $\tilde\omega_\varepsilon$ when $y\in C^c$), $k'(x,y)=k'(\theta_0,x,y)$, and $\tilde r_\varepsilon(x)=\int_{C^c}\tilde\omega_\varepsilon(x,y)|f(y)|K(x,dy)$, assumed finite for $x\in C$ (A3). Assume $f$ is integrable on $C^c$ against $K(\theta,x,\cdot)$ for $|\theta-\theta_0|<\varepsilon$, $x\in C$, so that $\tilde f(\theta,x)$ is a real number.
--
--   Let $v_0,v_1$ be finite non-negative measurable functions on $C$ with
--   $$(K(\theta)v_0)(x)\le v_0(x)-|\tilde f(\theta,x)|\quad(x\in C,\ |\theta-\theta_0|<\varepsilon),\tag{3.11}$$
--   $$(Kv_1)(x)\le v_1(x)-\int_C\omega_\varepsilon(x,y)v_0(y)K(x,dy)-\tilde r_\varepsilon(x)\quad(x\in C).\tag{3.12}$$
--
--   Then for every $x\in C$, $\theta\mapsto u^*(\theta,x)$ is differentiable at $\theta_0$, the function
--   $$y\mapsto\int_Ck'(y,z)u^*(\theta_0,z)K(y,dz)+\int_{C^c}k'(y,z)f(z)K(y,dz)$$
--   is $G(x,\cdot)$-integrable, and
--   $$u^{*\prime}(\theta_0,x)=\int G(x,dy)\Big[\int_Ck'(y,z)u^*(\theta_0,z)K(y,dz)+\int_{C^c}k'(y,z)f(z)K(y,dz)\Big].\tag{3.25}$$
--
--   This is part (I) of Theorem 3.1: the derivative formula for a random-horizon discounted expectation under one-step Lyapunov conditions, in the form (3.25) established in the proof (the printed (3.13) omits the term $GK'GK_{C^c}f$; see the goal theorem `theorem_3_1` for the correction and its counterexample). Part (II) of the theorem (continuity of the derivative on $[\theta_0-\varepsilon,\theta_0+\varepsilon]$) is stated separately.
--
--   **Formalization Note** The hypotheses are exactly those of `LyapDiffMC.RandomHorizon.theorem_3_1`; the conclusion is its clause (I). $k'$ is `kder` (the derivative within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$, the ordinary derivative at $\theta_0$), $\omega_\varepsilon$ and $\tilde r_\varepsilon$ are $[0,\infty]$-valued, and $u^*$ is the Green-measure integral `uStar` of the definition file.
-- source:
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 11, Theorem 3.1 (first claim), with the derivative in the form (3.25), p. 13

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- Theorem 3.1 (I) (p. 11), with the derivative in the proof's form (3.25) (p. 13): under A1–A3,
(3.11) and (3.12), `u*(·, x)` is differentiable at `θ₀` for every `x ∈ C`, and its derivative is
`∫ G(x, dy) [∫_C k′(y, z) u*(θ₀, z) K(y, dz) + ∫_{Cᶜ} k′(y, z) f(z) K(y, dz)]`, the outer integrand
being `G(x, ·)`-integrable. -/
theorem theorem_3_1_I {S : Type*} [MeasurableSpace S] (M : Setting S)
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
        + rtilde M k θ₀ ε x ≤ ENNReal.ofReal (v₁ x)) :
    -- (I): u*(·, x) is differentiable at θ₀, with derivative (3.25)
    (∀ x ∈ M.C,
      Integrable (fun y => (∫ z in M.C, kder k θ₀ ε θ₀ y z * uStar M θ₀ z ∂(discKernel M θ₀ y))
          + ∫ z in M.Cᶜ, kder k θ₀ ε θ₀ y z * M.f z ∂(discKernel M θ₀ y))
        (greenMeasure M θ₀ x) ∧
      HasDerivAt (fun θ => uStar M θ x)
        (∫ y, ((∫ z in M.C, kder k θ₀ ε θ₀ y z * uStar M θ₀ z ∂(discKernel M θ₀ y))
            + ∫ z in M.Cᶜ, kder k θ₀ ε θ₀ y z * M.f z ∂(discKernel M θ₀ y))
          ∂(greenMeasure M θ₀ x)) θ₀) := by sorry

end LyapDiffMC.RandomHorizon
