-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_theorem_4_1
-- name    : HubSpokePricing.Lagrangian.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:40.704466+00:00
-- url     : https://prove2.me/theorems/713db250-f754-4f76-94f6-f3723e570f5c
-- title:
--   Theorem 4.1, p. 17 — V^π(δ) ≤ V^OPT ≤ V^R ≤ V^π(δ) + r̄δ/(m − δ) + (r̄ + ω̄)ℙ[X₀(δ) = 0]
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $0\le\delta<m$, let $\lambda^*(\delta)$ be optimal to the perturbed dual (11), and let $\pi(\delta)$ be the corresponding Lagrangian policy (built from optimal solutions of (6) at $\lambda^*(\delta)$). Let $\mu$ be a stationary distribution of the original system under $\pi(\delta)$, with average revenue $V^{\pi(\delta)}=\sum_x\mu(x)R(x)$ and hub-depletion probability $\mathbb P[X_0(\delta)=0]$. Then for every initial state $x^0\in\mathcal X$,
--   $$V^{\pi(\delta)}\;\le\;V^{\mathrm{OPT}}(x^0)\;\le\;V^{\mathrm R}\;\le\;V^{\pi(\delta)}+\bar r\cdot\frac{\delta}{m-\delta}+(\bar r+\bar\omega)\cdot\mathbb P[X_0(\delta)=0].$$
--
--   The optimality gap of the Lagrangian policy is controlled by a perturbation term and by the stationary probability that the hub runs out of resources.
--
--   **Formalization Note** The paper states the theorem "for any $\lambda^*(\delta)$ optimal to (11)"; $0\le\delta<m$ is the range in which the fraction is meaningful (as in Corollary 4.7). $V^{\pi(\delta)}$ is the stationary average revenue, which by Corollary B.11 is the long-run average from every initial state. $V^{\mathrm{OPT}}$ uses a `limsup` and is bounded for every initial state.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 17, Theorem 4.1

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Theorem 4.1 (p. 17): for any `λ*(δ)` optimal to (11), the Lagrangian policy `π(δ)` satisfies
`V^π(δ) ≤ V^OPT ≤ V^R ≤ V^π(δ) + r̄ δ/(m − δ) + (r̄ + ω̄) ℙ[X₀(δ) = 0]`. -/
theorem theorem_4_1 (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m)
    (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (μ : OrigState N → ℝ) (hμ : MarkovChain.IsStationary (origKernel N sol) μ)
    (x0 : Fin N.n → ℕ) (hx0 : InX N x0) :
    Vpi N sol μ ≤ VOPT N x0 ∧ VOPT N x0 ≤ VRstar N ∧
      VRstar N ≤ Vpi N sol μ + N.rbar * δ / ((N.m : ℝ) - δ) +
        (N.rbar + N.omega) * hubEmptyProb N μ := by sorry

end HubSpokePricing.Lagrangian
