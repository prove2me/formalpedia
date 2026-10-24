-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_proof_3_1_bound
-- name    : LyapDiffMC.RandomHorizon.proof_3_1_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:40.082412+00:00
-- url     : https://prove2.me/theorems/3b37b659-9aba-4207-b3d4-ad8e04e60413
-- title:
--   Proof of Theorem 3.1, p. 12 — under (3.11): Σₙ Kⁿ(θ)|f̃(θ)| ≤ v₀, u*(θ) finite with |u*(θ)| ≤ v₀, and u*(θ) = f̃(θ) + K(θ)u*(θ)
-- statement:
--   Throughout, $S$ is a measurable state space, $(P(\theta):\theta\in\Lambda)$ a family of Markov transition kernels on $S$ indexed by an open interval $\Lambda=(a,b)$, $f, g : S\to\mathbb R$ measurable, and $\emptyset\neq C\subseteq S$ measurable. The non-negative kernel $K(\theta,x,dy)=e^{g(x)}P(\theta,x,dy)$ restricted to $y\in C$ is $K(\theta)$, its powers are $K^n(\theta)$ ($K^0(x,dy)=\delta_x(dy)$), $G(\theta,x,dy)=\sum_{n\ge0}K^n(\theta,x,dy)$ (possibly an infinite measure), $\tilde f(\theta,x)=f(x)+\int_{C^c}K(\theta,x,dy)f(y)$, and $u^*(\theta,x)=\sum_{n\ge0}(K^n(\theta)\tilde f(\theta))(x)=\int \tilde f(\theta,y)\,G(\theta,x,dy)$. Write $K=K(\theta_0)$ and $G=G(\theta_0)$.
--
--   Let $\varepsilon>0$ and assume $f$ is integrable on $C^c$ against $K(\theta,x,\cdot)$ for $|\theta-\theta_0|<\varepsilon$, $x\in C$. Let $v_0$ be a finite, non-negative, measurable function on $C$ with
--   $$(K(\theta)v_0)(x)\le v_0(x)-|\tilde f(\theta,x)|\qquad(x\in C,\ |\theta-\theta_0|<\varepsilon).\tag{3.11}$$
--   Then for every $\theta$ with $|\theta-\theta_0|<\varepsilon$ and every $x\in C$:
--   1. $\sum_{n\ge0}(K^n(\theta)|\tilde f(\theta)|)(x)=\int|\tilde f(\theta,y)|\,G(\theta,x,dy)\le v_0(x)$;
--   2. $\tilde f(\theta,\cdot)$ is $G(\theta,x,\cdot)$-integrable, so $u^*(\theta,x)=\sum_n(K^n(\theta)\tilde f(\theta))(x)$ is finite;
--   3. $|u^*(\theta,x)|\le v_0(x)$;
--   4. $u^*(\theta,\cdot)$ is integrable on $C$ against $K(\theta,x,\cdot)$, so $(K(\theta)u^*(\theta))(x)$ is finite;
--   5. $u^*(\theta,x)=\tilde f(\theta,x)+\int_Cu^*(\theta,y)K(\theta,x,dy)$, i.e. $u^*(\theta)=\tilde f(\theta)+K(\theta)u^*(\theta)$ on $C$ (3.2).
--
--   Item 5 at $\theta_0+h$ and $\theta_0$ gives the identity $(I-K)(u^*(\theta_0+h)-u^*(\theta_0))=(K(\theta_0+h)-K(\theta_0))u^*(\theta_0+h)+(\tilde f(\theta_0+h)-\tilde f(\theta_0))$ (3.19). That identity is the starting point of the continuity and differentiability arguments.
--
--   **Formalization Note** The Lyapunov inequalities are written additively in $[0,\infty]$ ($Kv+\dots\le v$), which is equivalent because $v_0,v_1$ are finite; $\omega_\varepsilon$ and $\tilde r_\varepsilon$ are $[0,\infty]$-valued. $k'$ is the derivative within $[\theta_0-\varepsilon,\theta_0+\varepsilon]$, the ordinary derivative at interior points. One $\varepsilon$ serves A2, A3 and the Lyapunov conditions, as in the paper's proof. The family $P(\theta)$ is given for all real $\theta$; only $\theta\in\Lambda$ matters. Under this mission's reading $u^*(\theta)=\sum_nK^n(\theta)\tilde f(\theta)$ holds by definition. The content of item 2 is that this series converges absolutely.
--
--   Differences from the source:
--   - reading: u*(θ, x) = the path expectation (3.1) for signed f → uStar M θ x = ∫ f̃(θ, y) G(θ, x, dy) = Σₙ (Kⁿ(θ)f̃(θ))(x); reason: for signed f the path expectation can be undefined while every hypothesis holds (Example C of the planning notes: E₀[2^T] = ∞ with f̃ ≡ 0); the proof works with Σₙ Kⁿ(θ)f̃(θ) (p. 12), the paper's own representation (2.2), (3.6), (3.8); the two agree whenever (3.1) converges absolutely, and milestone (3.8) ties them for f ≥ 0
--   - generalization: the hypotheses of Theorem 3.1 are in force (A1–A3, (3.11), (3.12)) → only (3.11), the finiteness of f̃ (hf_int) and measurable v₀ ≥ 0 on C are assumed; reason: this step uses only (3.11) and Proposition 3.1 (p. 12); under the theorem's hypotheses the statement specializes to the paper's
--   - generalization: u*(θ₀ + h) − u*(θ₀) = K(θ₀ + h)u*(θ₀ + h) − K(θ₀)u*(θ₀) + f̃(θ₀ + h) − f̃(θ₀), hence (3.19) → u*(θ, x) = f̃(θ, x) + ∫_C u*(θ, y) K(θ, x, dy) for every |θ − θ₀| < ε and x ∈ C ((3.2)), with K(θ)u*(θ) finite; reason: the displayed identity and (3.19) are the difference of (3.2) at θ₀ + h and at θ₀; stating (3.2) at every θ of the interval gives them for every |h| < ε
--   - encoding: separate ε's in A2, A3 and the theorem → one ε; reason: the proof takes the smallest of them (p. 12); shrinking ε keeps every hypothesis true, since ω_ε and r̃_ε only decrease
--   - encoding: f̃(θ, x) in (3.11) is a real number → hf_int : f integrable on Cᶜ against K(θ, x, ·) for |θ − θ₀| < ε, x ∈ C; reason: exactly the presupposition that the integral in (3.10) is finite, which (3.11) needs; it excludes only undefined cases (a Bochner integral would silently return 0)
--   - encoding: (K v)(x) ≤ v(x) − (non-negative terms) in (3.11), (3.12), (3.12′) → (K v)(x) + (the terms) ≤ v(x) in ℝ≥0∞; reason: every term lies in [0, ∞] and v(x) is finite, so the two forms are equivalent
--   - encoding: v₀, v₁ finite-valued non-negative functions on C → v₀ v₁ : S → ℝ, non-negative on C; reason: values off C never enter the statement; same instances
--   - encoding: measurability left implicit (f, g, C, the densities, v₀, v₁) → Measurable f, g, v₀, v₁, MeasurableSet C, Measurable (uncurry (k θ)) for θ ∈ Λ; reason: the paper's kernel integrals (Kh)(x) = ∫h(y)K(x, dy) are only defined for measurable h, and A1, A3 say '(measurable) density'
-- source:
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 12, proof of Theorem 3.1 (first paragraph, through (3.19))

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- Proof of Theorem 3.1, first step (p. 12). Under the Lyapunov bound (3.11) on
`|θ - θ₀| < ε`: `Σₙ Kⁿ(θ)|f̃(θ)| ≤ v₀`, so `f̃(θ)` is `G(θ, x, ·)`-integrable, `|u*(θ)| ≤ v₀`,
`K(θ)u*(θ)` is finite, and `u*(θ) = f̃(θ) + K(θ)u*(θ)` (3.2) on `C`. -/
theorem proof_3_1_bound {S : Type*} [MeasurableSpace S] (M : Setting S)
    (θ₀ ε : ℝ) (hε : 0 < ε)
    (hf_int : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      IntegrableOn M.f M.Cᶜ (discKernel M θ x))
    (v₀ : S → ℝ) (hv₀ : Measurable v₀) (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x)
    (h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x)) :
    ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y, ‖ftilde M θ y‖ₑ ∂(greenMeasure M θ x) ≤ ENNReal.ofReal (v₀ x) ∧
      Integrable (ftilde M θ) (greenMeasure M θ x) ∧
      |uStar M θ x| ≤ v₀ x ∧
      IntegrableOn (uStar M θ) M.C (discKernel M θ x) ∧
      uStar M θ x = ftilde M θ x + ∫ y in M.C, uStar M θ y ∂(discKernel M θ x) := by sorry

end LyapDiffMC.RandomHorizon
