-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_proof_3_1_continuity
-- name    : LyapDiffMC.RandomHorizon.proof_3_1_continuity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:44.203983+00:00
-- url     : https://prove2.me/theorems/8f234985-08e3-48c1-9ddc-043345595106
-- title:
--   Proof of Theorem 3.1, p. 12 — ∫_C G(x, dy)(|∫_C (K(θ₀ + h) − K(θ₀))(y, dz)u*(θ₀ + h, z)| + |f̃(θ₀ + h, y) − f̃(θ₀, y)|) ≤ |h|v₁(x); u* continuous at θ₀
-- statement:
--   Throughout, $S$ is a measurable state space, $(P(\theta):\theta\in\Lambda)$ a family of Markov transition kernels on $S$ indexed by an open interval $\Lambda=(a,b)$, $f, g : S\to\mathbb R$ measurable, and $\emptyset\neq C\subseteq S$ measurable. The non-negative kernel $K(\theta,x,dy)=e^{g(x)}P(\theta,x,dy)$ restricted to $y\in C$ is $K(\theta)$, its powers are $K^n(\theta)$ ($K^0(x,dy)=\delta_x(dy)$), $G(\theta,x,dy)=\sum_{n\ge0}K^n(\theta,x,dy)$ (possibly an infinite measure), $\tilde f(\theta,x)=f(x)+\int_{C^c}K(\theta,x,dy)f(y)$, and $u^*(\theta,x)=\sum_{n\ge0}(K^n(\theta)\tilde f(\theta))(x)=\int \tilde f(\theta,y)\,G(\theta,x,dy)$. Write $K=K(\theta_0)$ and $G=G(\theta_0)$.
--
--   Let $k(\theta,x,y)$ be a measurable density with $K(\theta,x,dy)=k(\theta,x,y)K(x,dy)$ for $\theta\in\Lambda$, $x\in C$ and all $y$ (A1 for $y\in C$, A3 for $y\in C^c$), such that $k(\cdot,x,y)$ is continuously differentiable on $[\theta_0-\varepsilon,\theta_0+\varepsilon]\subseteq\Lambda$ with derivative $k'(\cdot,x,y)$ (A2, A3). Put $\omega_\varepsilon(x,y)=\sup_{|\theta-\theta_0|<\varepsilon}|k'(\theta,x,y)|$ (written $\tilde\omega_\varepsilon$ when $y\in C^c$), $k'(x,y)=k'(\theta_0,x,y)$, and $\tilde r_\varepsilon(x)=\int_{C^c}\tilde\omega_\varepsilon(x,y)|f(y)|K(x,dy)$, assumed finite for $x\in C$ (A3). Assume $f$ is integrable on $C^c$ against $K(\theta,x,\cdot)$ for $|\theta-\theta_0|<\varepsilon$, $x\in C$, so that $\tilde f(\theta,x)$ is a real number.
--
--   Let $v_0,v_1$ be finite non-negative measurable functions on $C$ with
--   $$(K(\theta)v_0)(x)\le v_0(x)-|\tilde f(\theta,x)|\quad(x\in C,\ |\theta-\theta_0|<\varepsilon),\tag{3.11}$$
--   $$(Kv_1)(x)\le v_1(x)-\int_C\omega_\varepsilon(x,y)v_0(y)K(x,dy)-\tilde r_\varepsilon(x)\quad(x\in C).\tag{3.12}$$
--
--   (These are the hypotheses of Theorem 3.1.) Then for every $h$ with $|h|<\varepsilon$ and every $x\in C$,
--   $$\int_C G(x,dy)\Big(\Big|\int_C\big(K(\theta_0+h,y,dz)-K(\theta_0,y,dz)\big)u^*(\theta_0+h,z)\Big|+\big|\tilde f(\theta_0+h,y)-\tilde f(\theta_0,y)\big|\Big)\le|h|\,v_1(x),$$
--   and, for every $x\in C$, $\theta\mapsto u^*(\theta,x)$ is continuous at $\theta_0$.
--
--   This Lipschitz-type estimate on the right-hand side of (3.19), integrated against $G$, gives continuity of $u^*$ at $\theta_0$. Continuity in turn gives (3.21), which the dominated-convergence step for the derivative needs.
--
--   **Formalization Note** The Lyapunov inequalities are written additively in $[0,\infty]$ ($Kv+\dots\le v$), which is equivalent because $v_0,v_1$ are finite; $\omega_\varepsilon$ and $\tilde r_\varepsilon$ are $[0,\infty]$-valued. $k'$ is the derivative within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$, the ordinary derivative at interior points. One $\varepsilon$ serves A2, A3 and the Lyapunov conditions, as in the paper's proof. The family $P(\theta)$ is given for all real $\theta$; only $\theta\in\Lambda$ matters. The integral against the signed kernel $K(\theta_0+h)-K(\theta_0)$ is written as the difference of two finite integrals.
--
--   Differences from the source:
--   - reading: u*(θ, x) = the path expectation (3.1) for signed f → uStar M θ x = ∫ f̃(θ, y) G(θ, x, dy) = Σₙ (Kⁿ(θ)f̃(θ))(x); reason: for signed f the path expectation can be undefined while every hypothesis holds (Example C of the planning notes: E₀[2^T] = ∞ with f̃ ≡ 0); the proof works with Σₙ Kⁿ(θ)f̃(θ) (p. 12), the paper's own representation (2.2), (3.6), (3.8); the two agree whenever (3.1) converges absolutely, and milestone (3.8) ties them for f ≥ 0
--   - encoding: ∫_C (K(θ₀ + h, y, dz) − K(θ₀, y, dz))u*(θ₀ + h, z), an integral against a signed kernel → ∫_C u*(θ₀ + h, z)K(θ₀ + h, y, dz) − ∫_C u*(θ₀ + h, z)K(θ₀, y, dz), a difference of two Bochner integrals; reason: both integrals are finite (|u*(θ₀ + h)| ≤ v₀ and (3.11)), so the difference equals the signed-kernel integral
--   - encoding: ∫_C G(x, dy)(|…| + |…|) ≤ |h|v₁(x) → lintegral of ‖·‖ₑ against G(θ₀, x, ·) ≤ ofReal(|h| v₁(x)); reason: a non-negative integrand, so the integral is in [0, ∞]; same statement
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
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 12, proof of Theorem 3.1 ("Consequently, Proposition 3.1, together with the Lyapunov bound (3.12), ensures that")

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- Proof of Theorem 3.1, Lipschitz bound and continuity at `θ₀` (p. 12). Under the hypotheses
of Theorem 3.1, for `|h| < ε` and `x ∈ C`,
`∫_C G(x, dy)(|∫_C (K(θ₀ + h, y, dz) - K(θ₀, y, dz)) u*(θ₀ + h, z)| + |f̃(θ₀ + h, y) - f̃(θ₀, y)|)
≤ |h| v₁(x)`, and `u*(·, x)` is continuous at `θ₀`. -/
theorem proof_3_1_continuity {S : Type*} [MeasurableSpace S] (M : Setting S)
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
    (∀ h : ℝ, |h| < ε → ∀ x ∈ M.C,
      ∫⁻ y, (‖(∫ z in M.C, uStar M (θ₀ + h) z ∂(discKernel M (θ₀ + h) y))
              - ∫ z in M.C, uStar M (θ₀ + h) z ∂(discKernel M θ₀ y)‖ₑ
            + ‖ftilde M (θ₀ + h) y - ftilde M θ₀ y‖ₑ) ∂(greenMeasure M θ₀ x)
        ≤ ENNReal.ofReal (|h| * v₁ x)) ∧
    ∀ x ∈ M.C, ContinuousAt (fun θ => uStar M θ x) θ₀ := by sorry

end LyapDiffMC.RandomHorizon
