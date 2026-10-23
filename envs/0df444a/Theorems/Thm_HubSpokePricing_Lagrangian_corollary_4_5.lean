-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_corollary_4_5
-- name    : HubSpokePricing.Lagrangian.corollary_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:35.434578+00:00
-- url     : https://prove2.me/theorems/f22ed0c0-9e18-4ef9-b7ab-fec439d3e746
-- title:
--   Corollary 4.5, p. 20 — ℙ[X₀(δ) = 0] ≤ ℙ[X̃₀(δ) ≤ 0]
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $0\le\delta<m$, $\lambda^*(\delta)$ optimal to (11) and $\pi(\delta)$ the Lagrangian policy from optimal solutions $p_i$ of (6). Let $\mu$ be a stationary distribution of the original system under $\pi(\delta)$. Then
--   $$\mathbb P[X_0(\delta)=0]\;\le\;\mathbb P[\tilde X_0(\delta)\le0],$$
--   where the left side is the $\mu$-probability that the hub is empty, $\mu\{x:\sum_ix_i=m\}$, and the right side is the probability under the relaxed stationary law $\prod_ip_i(x_i)$ that $\sum_i x_i\ge m$.
--
--   The depletion probability of the original system is bounded by that of the relaxed system, in which spokes are independent.
--
--   **Formalization Note** $\mathbb P[\tilde X_0(\delta)\le0]$ is computed under $\prod_i p_i(x_i)$, the relaxed system's stationary law by Corollary B.10.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 20, Corollary 4.5

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Corollary 4.5 (p. 20): `ℙ[X₀(δ) = 0] ≤ ℙ[X̃₀(δ) ≤ 0]`. -/
theorem corollary_4_5 (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m)
    (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (μ : OrigState N → ℝ) (hμ : MarkovChain.IsStationary (origKernel N sol) μ) :
    hubEmptyProb N μ ≤ relaxDepletionProb N sol := by sorry

end HubSpokePricing.Lagrangian
