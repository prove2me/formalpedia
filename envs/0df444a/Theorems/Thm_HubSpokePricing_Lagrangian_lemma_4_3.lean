-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_lemma_4_3
-- name    : HubSpokePricing.Lagrangian.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:31.616211+00:00
-- url     : https://prove2.me/theorems/d1b9ec3e-07cb-47d0-997a-1ca920f29d4f
-- title:
--   Lemma 4.3, pp. 18–19 — V^R(δ) − V^π(δ) ≤ (r̄ + ω̄)(Σ_i q_{0i}) ℙ[X₀(δ) = 0] ≤ (r̄ + ω̄) ℙ[X₀(δ) = 0]
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $0\le\delta<m$, let $\lambda^*(\delta)$ be optimal to (11), and let $\pi(\delta)$ be the Lagrangian policy built from optimal solutions of (6) at $\lambda^*(\delta)$. Let $\mu$ be a stationary distribution of the original system under $\pi(\delta)$, $V^{\pi(\delta)}$ its average revenue under $\mu$, and $\mathbb P[X_0(\delta)=0]$ the $\mu$-probability that the hub is empty. Then
--   $$V^{\mathrm R}(\delta)-V^{\pi(\delta)}\;\le\;(\bar r+\bar\omega)\Big(\sum_{i\in[n]}q_{0i}\Big)\,\mathbb P[X_0(\delta)=0]\;\le\;(\bar r+\bar\omega)\,\mathbb P[X_0(\delta)=0].$$
--
--   The Lagrangian policy behaves identically in the relaxed and original systems except when a hub request arrives at an empty hub; each such event costs at most $\bar r+\bar\omega$.
--
--   **Formalization Note** The left side uses the value $V^{\mathrm R}(\delta)$ of (11), which the paper identifies with the relaxed system's average revenue by complementary slackness (p. 18). The stationary distribution is unique (Corollary B.11). The hypothesis $0\le\delta<m$ is the range on which (11) is used.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, pp. 18–19, Lemma 4.3

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Lemma 4.3 (pp. 18–19): for `λ*(δ)` optimal to (11) and the Lagrangian policy `π(δ)`,
`V^R(δ) − V^π(δ) ≤ (r̄ + ω̄)(∑ᵢ q_{0i}) ℙ[X₀(δ) = 0] ≤ (r̄ + ω̄) ℙ[X₀(δ) = 0]`. -/
theorem lemma_4_3 (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m)
    (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (μ : OrigState N → ℝ) (hμ : MarkovChain.IsStationary (origKernel N sol) μ) :
    VR N δ - Vpi N sol μ ≤ (N.rbar + N.omega) * (∑ i, N.qIn i) * hubEmptyProb N μ ∧
      (N.rbar + N.omega) * (∑ i, N.qIn i) * hubEmptyProb N μ ≤
        (N.rbar + N.omega) * hubEmptyProb N μ := by sorry

end HubSpokePricing.Lagrangian
