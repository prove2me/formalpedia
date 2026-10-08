-- Prove2me | Theorems.Thm_HuImkellerMuller_Power_theorem_14
-- name    : HuImkellerMuller.Power.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:42.105379+00:00
-- url     : https://prove2.me/theorems/6cb913ba-a27f-4a2d-95a2-c2fc0a0bde50
-- title:
--   Theorem 14, p. 17 — the power-utility value is (1/γ)x^γ exp(Y₀) for the unique bounded solution of the quadratic BSDE (15), attained by ρ* ∈ Π_{C_t}((Z_t + θ_t)/(1 − γ))
-- statement:
--   Let $W$ be an $m$-dimensional Brownian motion on $[0,T]$ with its augmented filtration $\mathbb F$, and let the market $(b,\sigma)$ with $d\le m$ stocks satisfy the standing hypotheses of §1 (predictable, uniformly bounded coefficients; $KI_d\ge\sigma\sigma^{\mathrm{tr}}\ge\varepsilon I_d$). Let $\tilde C\subseteq\mathbb R^{1\times d}$ be closed and nonempty, $C_t=\tilde C\sigma_t$, $\theta_t=\sigma_t^{\mathrm{tr}}(\sigma_t\sigma_t^{\mathrm{tr}})^{-1}b_t$, and $\gamma\in(0,1)$. Consider the power-utility problem (12),
--   $$
--   \bar V(x)=\sup_{\rho\in\tilde{\mathcal A}}E\Big[\frac1\gamma\big(X^{(\rho)}_T\big)^\gamma\Big],\qquad X^{(\rho)}_t=x\exp\Big(\int_0^t\rho_s\,dW_s+\int_0^t\rho_s\theta_s\,ds-\tfrac12\int_0^t|\rho_s|^2\,ds\Big).
--   $$
--   Then:
--
--   1. the BSDE (15), $Y_t=0-\int_t^TZ_s\,dW_s-\int_t^Tf(s,Z_s)\,ds$ with
--   $$
--   f(t,z)=\frac{\gamma(1-\gamma)}{2}\operatorname{dist}^2\Big(\frac1{1-\gamma}(z+\theta_t),C_t\Big)-\frac{\gamma|z+\theta_t|^2}{2(1-\gamma)}-\frac12|z|^2,
--   $$
--   has a solution $(Y,Z)\in\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$;
--   2. any two solutions agree ($Y$ a.s. at every time, $Z$ $\lambda\otimes P$-a.e.);
--   3. for every solution and every $x>0$,
--   $$
--   \bar V(x)=\frac1\gamma\,x^\gamma\exp(Y_0);
--   $$
--   4. for every solution there is $\rho^*\in\tilde{\mathcal A}$ with
--   $$
--   \rho^*_t\in\Pi_{C_t(\omega)}\Big(\frac1{1-\gamma}(Z_t+\theta_t)\Big)\quad\lambda\otimes P\text{-a.e.}\qquad(16)
--   $$
--   that attains $\bar V(x)$ for every $x>0$.
--
--   This is the BSDE characterization of constrained power-utility maximization with a closed, not necessarily convex, constraint set.
--
--   **Formalization Note** The page prints $V(x)=x^\gamma\exp(Y_0)$, while (12) maximizes $E[U_\gamma(X_T)]$ with $U_\gamma(x)=\frac1\gamma x^\gamma$; the proof computes $E[(X_T)^\gamma]=x^\gamma\exp(Y_0)$, using $x^\gamma$ as the utility. The value of (12) as defined is therefore $\frac1\gamma x^\gamma\exp(Y_0)$, which is what is stated. Further conventions: $\tilde C\neq\emptyset$ is added; strategies are written in $\rho=\tilde\rho\sigma\in\mathbb R^m$; (16) is read $\lambda\otimes P$-a.e.; $Y_0$ is a.s. constant and part 3 holds for $P$-a.e. $\omega$; expectations are lower integrals in $[0,\infty]$; stochastic integrals are given by an Itô-integral operator `I`; the paper's §3 constraint set "$\bar C_2\subseteq\mathbb R^d$" and $\tilde C$ are one closed set of row vectors.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, Theorem 14, p. 17; problem (12) and Definition 13, p. 16; (11), pp. 15–16

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Strategy
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

/-- Theorem 14, p. 17: the BSDE (15) has a unique solution `(Y, Z) ∈ ℋ^∞(ℝ) × ℋ²(ℝᵐ)`; for
every solution and every `x > 0` the value of (12) with `U_γ(x) = x^γ/γ` is
`(1/γ) x^γ exp(Y₀)`; and an admissible `ρ*` with (16) attains it. -/
theorem theorem_14
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)} (hW : EthierKurtz.IsStandardBrownian P W)
    {𝓕 : Filtration ℝ≥0 mΩ}
    (h𝓕 : CvitanicKaratzas92.Optimality.IsAugmentedBrownianFiltration P W 𝓕)
    {I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ}
    (hI : CvitanicKaratzas92.Optimality.IsItoIntegralOperator P 𝓕 T W I)
    {b : ℝ≥0 → Ω → (Fin d → ℝ)} {σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ}
    (hmkt : MarketHyp P 𝓕 T b σ)
    {Ct : Set (Fin d → ℝ)} (hCt : IsClosed Ct) (hne : Ct.Nonempty)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∃ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)),
      IsSolution15 P 𝓕 T I b σ Ct γ Y Z) ∧
    (∀ (Y₁ Y₂ : ℝ≥0 → Ω → ℝ) (Z₁ Z₂ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)),
      IsSolution15 P 𝓕 T I b σ Ct γ Y₁ Z₁ → IsSolution15 P 𝓕 T I b σ Ct γ Y₂ Z₂ →
        (∀ t ≤ T, Y₁ t =ᵐ[P] Y₂ t) ∧
          ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
            Z₁ q.1.toNNReal q.2 = Z₂ q.1.toNNReal q.2) ∧
    (∀ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)),
      IsSolution15 P 𝓕 T I b σ Ct γ Y Z → ∀ x : ℝ, 0 < x →
        ∀ᵐ ω ∂P, value P 𝓕 T I b σ Ct γ x
          = ENNReal.ofReal (1 / γ * x ^ γ * Real.exp (Y 0 ω))) ∧
    (∀ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)),
      IsSolution15 P 𝓕 T I b σ Ct γ Y Z →
        ∃ ρstar : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m),
          Admissible P 𝓕 T σ Ct ρstar ∧
          (∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
            ρstar q.1.toNNReal q.2 ∈ HuImkellerMuller.Exponential.proj (HuImkellerMuller.Exponential.Cset Ct σ q.1.toNNReal q.2)
              ((1 / (1 - γ)) • (Z q.1.toNNReal q.2 + HuImkellerMuller.Exponential.theta b σ q.1.toNNReal q.2))) ∧
          ∀ x : ℝ, 0 < x →
            ∫⁻ ω, ENNReal.ofReal ((wealth I b σ x ρstar T ω) ^ γ / γ) ∂P
              = value P 𝓕 T I b σ Ct γ x) := by sorry

end HuImkellerMuller.Power
