-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_proof_3_1_derivative_equation
-- name    : LyapDiffMC.RandomHorizon.proof_3_1_derivative_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:40.794062+00:00
-- url     : https://prove2.me/theorems/c886def1-e559-443e-a092-fbd579284258
-- title:
--   Proof of Theorem 3.1, p. 13 (corrected: one-sided at θ₀ ± ε) — u*′(θ) = f̃′(θ) + K′(θ)u*(θ) + K(θ)u*′(θ) on [θ₀ − ε, θ₀ + ε]
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
--   and, for every $\theta\in[\theta_0-\varepsilon,\theta_0+\varepsilon]$ and $x\in C$,
--   $$(K(\theta)v_1)(x)\le v_1(x)-\int_C\omega_\varepsilon(x,y)v_0(y)K(\theta,x,dy)-\int_{C^c}\tilde\omega_\varepsilon(x,y)|f(y)|K(\theta,x,dy).\tag{3.12$'$}$$
--   Then for every $\theta\in[\theta_0-\varepsilon,\theta_0+\varepsilon]$ and $x\in C$, $u^*(\cdot,x)$ has a derivative $u^{*\prime}(\theta,x)$ within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$. It is one-sided at the endpoints. Moreover
--   $$u^{*\prime}(\theta,x)=\tilde f'(\theta,x)+(K'(\theta)u^*(\theta))(x)+(K(\theta)u^{*\prime}(\theta))(x),$$
--   where
--   $$\tilde f'(\theta,x)=\int_{C^c}k'(\theta,x,y)f(y)K(x,dy),\qquad (K'(\theta)u^*(\theta))(x)=\int_Ck'(\theta,x,y)u^*(\theta,y)K(x,dy),$$
--   with $K=K(\theta_0)$, and $(K(\theta)u^{*\prime}(\theta))(x)=\int_Cu^{*\prime}(\theta,y)K(\theta,x,dy)$. All three integrands are integrable, and $\tilde f'(\theta,x)$ above is the derivative of $\tilde f(\cdot,x)$ within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$.
--
--   This is the differentiated form of (3.2) on the whole interval. Inverting $I-K(\theta)$ through $G(\theta)$ expresses $u^{*\prime}(\theta+h)-u^{*\prime}(\theta)$ as four $G(\theta)$-integrals, and these drive the proof of continuity of $u^{*\prime}$.
--
--   **Formalization Note** The Lyapunov inequalities are written additively in $[0,\infty]$ ($Kv+\dots\le v$), which is equivalent because $v_0,v_1$ are finite; $\omega_\varepsilon$ and $\tilde r_\varepsilon$ are $[0,\infty]$-valued. $k'$ is the derivative within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$, the ordinary derivative at interior points. One $\varepsilon$ serves A2, A3 and the Lyapunov conditions, as in the paper's proof. The family $P(\theta)$ is given for all real $\theta$; only $\theta\in\Lambda$ matters. $u^{*\prime}(\theta,x)$ is the derivative of $u^*(\cdot,x)$ within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$.
--
--   Differences from the source:
--   - correction: u*′(θ) = f̃′(θ) + K′(θ)u*(θ) + K(θ)u*′(θ) for θ ∈ [θ₀ − ε, θ₀ + ε], with u*′ the (two-sided) derivative → the derivative within [θ₀ − ε, θ₀ + ε] (one-sided at the endpoints θ₀ ± ε); reason: with two-sided derivatives the claim is false at θ₀ ± ε: Example B (S = {0, 1}, C = {0}, g = 0, P(θ, 0, 0) = 1/2 for |θ| ≤ 1/2 and 1/4 otherwise, Λ = (−1, 1), θ₀ = 0, ε = 1/2, f(0) = 1, f(1) = 0, v₀ = 2, v₁ = 0) satisfies every hypothesis, but u*(±1/2, 0) = 2 while u*(θ, 0) = 4/3 for |θ| > 1/2
--   - reading: u*(θ, x) = the path expectation (3.1) for signed f → uStar M θ x = ∫ f̃(θ, y) G(θ, x, dy) = Σₙ (Kⁿ(θ)f̃(θ))(x); reason: for signed f the path expectation can be undefined while every hypothesis holds (Example C of the planning notes: E₀[2^T] = ∞ with f̃ ≡ 0); the proof works with Σₙ Kⁿ(θ)f̃(θ) (p. 12), the paper's own representation (2.2), (3.6), (3.8); the two agree whenever (3.1) converges absolutely, and milestone (3.8) ties them for f ≥ 0
--   - encoding: f̃′(θ), the derivative of f̃(θ, x) = f(x) + ∫_{Cᶜ} k(θ, x, y)f(y)K(x, dy), not written out → ∫_{Cᶜ} k′(θ, x, y)f(y)K(x, dy), with an extra conclusion that this is the derivative of f̃(·, x) within [θ₀ − ε, θ₀ + ε]; reason: the derivative of (3.10) under A3, stated explicitly so that the f̃′ term is the derivative of f̃ (one-sided at the endpoints, as for u*′); at θ₀ it is the second term of (3.25)
--   - encoding: K′(θ)u*(θ, x), f̃′(θ, x), (K(θ)u*′(θ))(x) as real numbers → extra conclusions: the three integrands are integrable; reason: rules out junk-zero Bochner integrals; these are presuppositions of the printed equation
--   - encoding: (3.14) and (3.12′) as hypotheses of the second clause of Theorem 3.1 → h314, h312' as binders (with (3.12′) written additively in ℝ≥0∞); reason: the paper invokes them for this step (p. 13)
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
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 13, proof of Theorem 3.1 ("Turning to the continuity of u*′(·, x)")

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- Proof of Theorem 3.1, derivative equation on the interval (p. 13). Under the hypotheses of
Theorem 3.1 together with (3.14) and (3.12′), for every `θ ∈ [θ₀ - ε, θ₀ + ε]` and `x ∈ C`,
`u*(·, x)` has a derivative `u*′(θ, x)` within `[θ₀ - ε, θ₀ + ε]`, `f̃(·, x)` has the derivative
`f̃′(θ, x) = ∫_{Cᶜ} k′(θ, x, y) f(y) K(x, dy)` within `[θ₀ - ε, θ₀ + ε]`, and
`u*′(θ) = f̃′(θ) + K′(θ)u*(θ) + K(θ)u*′(θ)`, where
`K′(θ)u*(θ, x) = ∫_C k′(θ, x, y) u*(θ, y) K(x, dy)` and `K = K(θ₀)`. -/
theorem proof_3_1_derivative_equation {S : Type*} [MeasurableSpace S] (M : Setting S)
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
    ∀ θ ∈ Set.Icc (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      HasDerivWithinAt (fun t => uStar M t x)
        (derivWithin (fun t => uStar M t x) (Set.Icc (θ₀ - ε) (θ₀ + ε)) θ)
        (Set.Icc (θ₀ - ε) (θ₀ + ε)) θ ∧
      IntegrableOn (fun y => kder k θ₀ ε θ x y * M.f y) M.Cᶜ (discKernel M θ₀ x) ∧
      HasDerivWithinAt (fun t => ftilde M t x)
        (∫ y in M.Cᶜ, kder k θ₀ ε θ x y * M.f y ∂(discKernel M θ₀ x))
        (Set.Icc (θ₀ - ε) (θ₀ + ε)) θ ∧
      IntegrableOn (fun y => kder k θ₀ ε θ x y * uStar M θ y) M.C (discKernel M θ₀ x) ∧
      IntegrableOn (fun y => derivWithin (fun t => uStar M t y) (Set.Icc (θ₀ - ε) (θ₀ + ε)) θ)
        M.C (discKernel M θ x) ∧
      derivWithin (fun t => uStar M t x) (Set.Icc (θ₀ - ε) (θ₀ + ε)) θ
        = (∫ y in M.Cᶜ, kder k θ₀ ε θ x y * M.f y ∂(discKernel M θ₀ x))
          + (∫ y in M.C, kder k θ₀ ε θ x y * uStar M θ y ∂(discKernel M θ₀ x))
          + ∫ y in M.C, derivWithin (fun t => uStar M t y) (Set.Icc (θ₀ - ε) (θ₀ + ε)) θ
              ∂(discKernel M θ x) := by sorry

end LyapDiffMC.RandomHorizon
