-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_theorem_3_1
-- name    : LyapDiffMC.RandomHorizon.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:41.534983+00:00
-- url     : https://prove2.me/theorems/627662e1-9dd8-4590-9c19-bcaa1254ceed
-- title:
--   Theorem 3.1, p. 11 — Lyapunov conditions for differentiability of a random-horizon discounted Markov chain expectation (corrected: derivative as in (3.25); one-sided at the endpoints)
-- statement:
--   Throughout, $S$ is a measurable state space, $(P(\theta):\theta\in\Lambda)$ a family of Markov transition kernels on $S$ indexed by an open interval $\Lambda=(a,b)$, $f, g : S\to\mathbb R$ measurable, and $\emptyset\neq C\subseteq S$ measurable. The non-negative kernel $K(\theta,x,dy)=e^{g(x)}P(\theta,x,dy)$ restricted to $y\in C$ is $K(\theta)$, its powers are $K^n(\theta)$ ($K^0(x,dy)=\delta_x(dy)$), $G(\theta,x,dy)=\sum_{n\ge0}K^n(\theta,x,dy)$ (possibly an infinite measure), $\tilde f(\theta,x)=f(x)+\int_{C^c}K(\theta,x,dy)f(y)$, and $u^*(\theta,x)=\sum_{n\ge0}(K^n(\theta)\tilde f(\theta))(x)=\int \tilde f(\theta,y)\,G(\theta,x,dy)$. Write $K=K(\theta_0)$ and $G=G(\theta_0)$.
--
--   Let $k(\theta,x,y)$ be a measurable density with $K(\theta,x,dy)=k(\theta,x,y)K(x,dy)$ for $\theta\in\Lambda$, $x\in C$ and all $y$ (A1 for $y\in C$, A3 for $y\in C^c$), such that $k(\cdot,x,y)$ is continuously differentiable on $[\theta_0-\varepsilon,\theta_0+\varepsilon]\subseteq\Lambda$ with derivative $k'(\cdot,x,y)$ (A2, A3). Put $\omega_\varepsilon(x,y)=\sup_{|\theta-\theta_0|<\varepsilon}|k'(\theta,x,y)|$ (written $\tilde\omega_\varepsilon$ when $y\in C^c$), $k'(x,y)=k'(\theta_0,x,y)$, and $\tilde r_\varepsilon(x)=\int_{C^c}\tilde\omega_\varepsilon(x,y)|f(y)|K(x,dy)$, assumed finite for $x\in C$ (A3). Assume $f$ is integrable on $C^c$ against $K(\theta,x,\cdot)$ for $|\theta-\theta_0|<\varepsilon$, $x\in C$, so that $\tilde f(\theta,x)$ is a real number.
--
--   Let $v_0,v_1$ be finite non-negative measurable functions on $C$ with
--   $$(K(\theta)v_0)(x)\le v_0(x)-|\tilde f(\theta,x)|\quad(x\in C,\ |\theta-\theta_0|<\varepsilon),\tag{3.11}$$
--   $$(Kv_1)(x)\le v_1(x)-\int_C\omega_\varepsilon(x,y)v_0(y)K(x,dy)-\tilde r_\varepsilon(x)\quad(x\in C).\tag{3.12}$$
--
--   **(I)** For every $x\in C$, $\theta\mapsto u^*(\theta,x)$ is differentiable at $\theta_0$, and
--   $$u^{*\prime}(\theta_0,x)=\int_CG(x,dy)\int_Ck'(y,z)u^*(\theta_0,z)K(y,dz)+\int_CG(x,dy)\int_{C^c}k'(y,z)f(z)K(y,dz),\tag{3.25}$$
--   where the outer integrand is $G(x,\cdot)$-integrable.
--
--   **(II)** If, in addition,
--   $$\int_C\omega_\varepsilon(x,y)v_1(y)K(x,dy)<\infty\quad(x\in C)\tag{3.14}$$
--   and (3.12) holds on the whole interval, i.e. for $\theta\in[\theta_0-\varepsilon,\theta_0+\varepsilon]$ and $x\in C$,
--   $$(K(\theta)v_1)(x)\le v_1(x)-\int_C\omega_\varepsilon(x,y)v_0(y)K(\theta,x,dy)-\int_{C^c}\tilde\omega_\varepsilon(x,y)|f(y)|K(\theta,x,dy),\tag{3.12$'$}$$
--   then for every $x\in C$, $u^*(\cdot,x)$ is continuously differentiable on $[\theta_0-\varepsilon,\theta_0+\varepsilon]$, with one-sided derivatives at the endpoints.
--
--   Here $u^*(\theta,x)$ is the expected discounted reward $\mathbf E^\theta_x[\sum_{j<T}e^{\sum_{k<j}g(X_k)}f(X_j)+e^{\sum_{k<T}g(X_k)}f(X_T)]$ collected until the chain driven by $P(\theta)$ first leaves $C$, represented as $\sum_nK^n(\theta)\tilde f(\theta)$. $T$ may be infinite, and no moment condition on $T$ is assumed. The functions $v_0,v_1$ are stochastic Lyapunov functions. The theorem gives derivative formulas for such expectations, including in the discount exponent $g$, under conditions checkable from the one-step model.
--
--   **Formalization Note** The Lyapunov inequalities are written additively in $[0,\infty]$ ($Kv+\dots\le v$), which is equivalent because $v_0,v_1$ are finite; $\omega_\varepsilon$ and $\tilde r_\varepsilon$ are $[0,\infty]$-valued. $k'$ is the derivative within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$, the ordinary derivative at interior points. One $\varepsilon$ serves A2, A3 and the Lyapunov conditions, as in the paper's proof. The family $P(\theta)$ is given for all real $\theta$; only $\theta\in\Lambda$ matters. The integrability clause in (I) makes the formula's integral a genuine finite integral.
--
--   Differences from the source:
--   - correction: (3.13): u*′(θ₀) = ∫_C∫_C∫_C G(x, dy)K′(y, dz)G(z, dw)f(w) + ∫_C∫_{Cᶜ} G(x, dy)K′(y, dz)f(z) → (3.25): u*′(θ₀, x) = ∫ G(x, dy)[∫_C k′(y, z)u*(θ₀, z)K(y, dz) + ∫_{Cᶜ} k′(y, z)f(z)K(y, dz)]; reason: (3.13) has f(w) where the proof's (3.25) has u*(θ₀, z) = ∫G(z, dw)f̃(θ₀, w), so it drops G K′ G K_{Cᶜ} f; Example A (S = {0, 1}, C = {0}, g = 0, P(θ, 0, 0) = θ, Λ = (0, 1), θ₀ = 1/2, f(0) = 0, f(1) = 1, v₀ = 1, v₁ = 4) satisfies every hypothesis, u*(θ, 0) = 1 for all θ so u*′(θ₀) = 0 = (3.25), but (3.13) = −2
--   - correction: u*′(·, x) continuous on [θ₀ − ε, θ₀ + ε] (two-sided derivative) → the derivative within [θ₀ − ε, θ₀ + ε] (one-sided at the endpoints θ₀ ± ε); reason: with two-sided derivatives the claim is false at θ₀ ± ε: Example B (S = {0, 1}, C = {0}, g = 0, P(θ, 0, 0) = 1/2 for |θ| ≤ 1/2 and 1/4 otherwise, Λ = (−1, 1), θ₀ = 0, ε = 1/2, f(0) = 1, f(1) = 0, v₀ = 2, v₁ = 0) satisfies every hypothesis, but u*(±1/2, 0) = 2 while u*(θ, 0) = 4/3 for |θ| > 1/2
--   - reading: u*(θ, x) = the path expectation (3.1) for signed f → uStar M θ x = ∫ f̃(θ, y) G(θ, x, dy) = Σₙ (Kⁿ(θ)f̃(θ))(x); reason: for signed f the path expectation can be undefined while every hypothesis holds (Example C of the planning notes: E₀[2^T] = ∞ with f̃ ≡ 0); the proof works with Σₙ Kⁿ(θ)f̃(θ) (p. 12), the paper's own representation (2.2), (3.6), (3.8); the two agree whenever (3.1) converges absolutely, and milestone (3.8) ties them for f ≥ 0
--   - encoding: u*′(θ₀) given by a real-valued integral (finite by (3.24)) → an extra conclusion: the integrand of (3.25) is G(θ₀, x, ·)-integrable; reason: rules out a junk-zero Bochner integral; it is a conclusion, so it adds content and removes none
--   - encoding: 'u*′(·, x) is continuous on [θ₀ − ε, θ₀ + ε]' → ContDiffOn ℝ 1 (fun θ => u*(θ, x)) (Icc (θ₀ − ε) (θ₀ + ε)); reason: u* is differentiable (within the interval) with continuous derivative there; this is the paper's claim with the endpoint correction above
--   - encoding: separate ε's in A2, A3 and the theorem → one ε; reason: the proof takes the smallest of them (p. 12); shrinking ε keeps every hypothesis true, since ω_ε and r̃_ε only decrease
--   - encoding: k(·, x, y) defined on Λ and differentiable on [θ₀ − ε, θ₀ + ε] → hεΛ : [θ₀ − ε, θ₀ + ε] ⊆ Λ = (a, b); reason: implied: A2 speaks of k on [θ₀ − ε, θ₀ + ε] and k(θ, ·, ·) is only defined for θ ∈ Λ
--   - encoding: P(θ) given for θ ∈ Λ → P θ given for every θ ∈ ℝ, constrained only for θ ∈ Λ; reason: extend the family by P(θ₀) outside Λ; no instance changes
--   - encoding: f̃(θ, x) in (3.11) is a real number → hf_int : f integrable on Cᶜ against K(θ, x, ·) for |θ − θ₀| < ε, x ∈ C; reason: exactly the presupposition that the integral in (3.10) is finite, which (3.11) needs; it excludes only undefined cases (a Bochner integral would silently return 0)
--   - encoding: K(θ, x, dy) = k(θ, x, y)K(x, dy) (A1 for y ∈ C, A3 for y ∈ Cᶜ) → one function k on S × S, K(θ, x, ·) = K(θ₀, x, ·).withDensity (ofReal ∘ k(θ, x, ·)) for θ ∈ Λ, x ∈ C, and hk_nonneg: k(θ, x, ·) ≥ 0 K(θ₀, x, ·)-a.e.; reason: the two densities of A1 and A3 live on the disjoint sets C and Cᶜ; a density of a non-negative measure is a.e. non-negative, so hk_nonneg is implied by the printed equation (withDensity of ofReal sees only k⁺)
--   - encoding: measurability left implicit (f, g, C, the densities, v₀, v₁) → Measurable f, g, v₀, v₁, MeasurableSet C, Measurable (uncurry (k θ)) for θ ∈ Λ; reason: the paper's kernel integrals (Kh)(x) = ∫h(y)K(x, dy) are only defined for measurable h, and A1, A3 say '(measurable) density'
--   - encoding: (K v)(x) ≤ v(x) − (non-negative terms) in (3.11), (3.12), (3.12′) → (K v)(x) + (the terms) ≤ v(x) in ℝ≥0∞; reason: every term lies in [0, ∞] and v(x) is finite, so the two forms are equivalent
--   - encoding: v₀, v₁ finite-valued non-negative functions on C → v₀ v₁ : S → ℝ, non-negative on C; reason: values off C never enter the statement; same instances
--   - encoding: ω_ε(x, y) = sup{|k′(θ, x, y)| : |θ − θ₀| < ε}, ω̃_ε, r̃_ε → ℝ≥0∞-valued iSup (omega) and lintegral (rtilde); reason: the supremum may be +∞; a real supremum would return 0 on an unbounded set
--   - encoding: k′(θ, x, y), the derivative of k(·, x, y) on [θ₀ − ε, θ₀ + ε] → kder = derivWithin on Icc (θ₀ − ε) (θ₀ + ε); reason: the ordinary derivative at interior points (in particular at θ₀), the one-sided one at the endpoints, as A2's 'in [θ₀ − ε, θ₀ + ε]'
-- source:
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 11, Theorem 3.1 (with (3.25), p. 13)

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- Theorem 3.1 (p. 11), with the derivative in the proof's form (3.25) (p. 13) and the
continuity clause read with one-sided derivatives at the endpoints of `[θ₀ - ε, θ₀ + ε]`.
`Λ = (a, b)`; `k` is the density of A1 (targets in `C`) and A3 (targets in `Cᶜ`) with respect to
`K(θ₀)`; `v₀`, `v₁` are the Lyapunov functions of (3.11), (3.12); clause (II) adds (3.14) and
(3.12′). -/
theorem theorem_3_1 {S : Type*} [MeasurableSpace S] (M : Setting S)
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
          ∂(greenMeasure M θ₀ x)) θ₀) ∧
    -- (II): under (3.14) and (3.12′), u*(·, x) is C¹ on [θ₀ - ε, θ₀ + ε]
    ((∀ x ∈ M.C,
        ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x) < ⊤) →
     (∀ θ ∈ Set.Icc (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
        ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ x)
          + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ x)
          + ∫⁻ y in M.Cᶜ, omega k θ₀ ε x y * ‖M.f y‖ₑ ∂(discKernel M θ x)
          ≤ ENNReal.ofReal (v₁ x)) →
     ∀ x ∈ M.C, ContDiffOn ℝ 1 (fun θ => uStar M θ x) (Set.Icc (θ₀ - ε) (θ₀ + ε))) := by sorry

end LyapDiffMC.RandomHorizon
