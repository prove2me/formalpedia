-- Prove2me | Theorems.Thm_LookbackMOT_HL_theorem_3_1
-- name    : LookbackMOT.HL.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:45.083487+00:00
-- url     : https://prove2.me/theorems/47463f82-aed1-443e-8d93-012d9caf8001
-- title:
--   Theorem 3.1, p. 12 — U^μ(g(X*_T)) = μ(λ*) + J(λ*, τ*) = μ^HL(g) for the reduced problem (3.7)
-- statement:
--   Let $B$ be an $(\mathcal F_t)$-Brownian motion and $X_t=X_0+B_t$. Let $\mu$ be a probability measure on $\mathbb R$ with finite first moment and mean $\int x\,\mu(dx)=X_0$, and let $\xi=g(X^*)$ for a $C^1$ nondecreasing $g:\mathbb R\to\mathbb R_+$ such that
--   $$\sup_{\tau\in\mathcal T_\infty}\mathbb E\big[g(X^*_\tau)\big]<\infty\qquad\text{and}\qquad\mu^{HL}(g)<\infty,$$
--   where $\mu^{HL}$ is the Hardy–Littlewood transform of $\mu$ (3.12). Let $\tau^*$ be the Azéma–Yor stopping time (3.13) and $\lambda^*$ the multiplier (3.14). Then the reduced robust superhedging cost (3.7) satisfies
--   $$U^\mu(\xi)=\inf_{\lambda\in\Lambda^\mu_0}\big\{\mu(\lambda)+u^\lambda(X_0,X_0)\big\}=\mu(\lambda^*)+J(\lambda^*,\tau^*)=\mu^{HL}(g).$$
--
--   The theorem recovers, through the dual stochastic control formulation, Hobson's model-free upper bound for lookback options: given the prices of all European calls at maturity, the cheapest superhedge of $g(X^*_T)$ costs exactly the price of $g$ under the Hardy–Littlewood transform of the marginal, and the optimal multiplier and stopping time are given explicitly by the Azéma–Yor construction.
--
--   **Formalization Note** $U^\mu(\xi)$ is the reduced problem (3.7), which the paper introduces on p. 11 ("we are reduced to the problem … (3.7)") and for which Sections 3.3–3.4 prove the theorem. The passage from the superhedging problem (2.6), which needs stochastic integrals, to (3.7) rests on Proposition 2.1, the claim (3.4) and Proposition 3.1, which are not part of this mission. Accordingly the hypothesis $\sup_{\mathbb P\in\mathcal P_\infty}\mathbb E^{\mathbb P}[\xi^+]<\infty$ is stated through Proposition 3.1 with $\lambda=0$ as $\sup_{\tau\in\mathcal T_\infty}\mathbb E[g(X^*_\tau)]<\infty$, and the horizon $T$ is gone (infinite-horizon stopping over $\mathcal T_\infty$). The mean condition and the integrability of $\mu$ (p. 7) are assumed; the spot $X_0$ is any real number (the paper's $X_0>0$ is not needed for $\mu\in M(\mathbb R)$). $\mu^{HL}$ enters as a measure satisfying its defining identity. $\lambda^*$ is (3.14) in the change-of-variables form $\int_{X_0<m<r^\mu} g'(m)(x-b^{-1}(m))^+/(m-b^{-1}(m))\,dm$ that the proof of Lemma 3.3 uses (solution of (3.21) with $\psi=b^{-1}$); it coincides with the page's $b(d\xi)$ formula when $b$ is continuous, and where $\mu$ has atoms the Lebesgue–Stieltjes reading can fail to be $\mu$-integrable, which would make the theorem false. All value functions are extended reals; $\mu(\lambda^*)$ and $\mu^{HL}(g)$ are real integrals. The Brownian motion lives on an arbitrary filtered probability space.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 12, Theorem 3.1 (with (3.7), p. 11, and (3.12)–(3.14), p. 12)

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : IsFBrownian P ℱ B)
    (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (hξ : (⨆ τ : Ω → WithTop ℝ≥0, ⨆ (_ : IsUIStop P ℱ (shift X₀ B) τ),
      ∫⁻ ω, ENNReal.ofReal (g (runMaxUpTo (shift X₀ B) τ ω)) ∂P) < ⊤)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    U P ℱ B X₀ μ g = ((∫ x, lamStar μ X₀ g x ∂μ : ℝ) : EReal) +
        J P B X₀ g (lamStar μ X₀ g) (tauStar B X₀ μ) ∧
      ((∫ x, lamStar μ X₀ g x ∂μ : ℝ) : EReal) + J P B X₀ g (lamStar μ X₀ g) (tauStar B X₀ μ) =
        ((∫ x, g x ∂ν : ℝ) : EReal) := by sorry

end LookbackMOT.HL
