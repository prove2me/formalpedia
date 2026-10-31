-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_lemma_4_2
-- name    : HubSpokePricing.Lagrangian.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:27.951247+00:00
-- url     : https://prove2.me/theorems/56fabed8-3136-4677-aead-d84a3f9801b9
-- title:
--   Lemma 4.2, p. 18 — V^R(δ) ≤ V^R(0) = V^R ≤ V^R(δ) + r̄·δ/(m − δ)
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $\bar V^\lambda=m\lambda+\sum_i h_i^\lambda$ with $h_i^\lambda$ the optimal value of (6), and for $\delta\ge0$ let $V^{\mathrm R}(\delta)=\min_{\lambda\ge0}\bar V^\lambda-\delta\lambda$ be the value of the perturbed dual (11), so that $V^{\mathrm R}=V^{\mathrm R}(0)$ is the Lagrangian bound (9). For $0\le\delta<m$,
--   $$V^{\mathrm R}(\delta)\;\le\;V^{\mathrm R}(0)=V^{\mathrm R}\;\le\;V^{\mathrm R}(\delta)+\bar r\cdot\frac{\delta}{m-\delta}.$$
--
--   Perturbing the dual by $\delta$ (asking the hub to keep $\delta$ resources on average) costs at most $\bar r\,\delta/(m-\delta)$ in the bound.
--
--   **Formalization Note** The range $0\le\delta<m$ is the paper's ("for any $\delta<m$", p. 18; Corollary 4.7 states $0\le\delta<m$) and is needed for $\delta/(m-\delta)$ to be meaningful. $V^{\mathrm R}(0)=V^{\mathrm R}$ holds by definition.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 18, Lemma 4.2, (12)

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Lemma 4.2 (p. 18): `V^R(δ) ≤ V^R(0) = V^R ≤ V^R(δ) + r̄ δ / (m − δ)` for `0 ≤ δ < m`. -/
theorem lemma_4_2 (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m) :
    VR N δ ≤ VRstar N ∧ VRstar N ≤ VR N δ + N.rbar * δ / ((N.m : ℝ) - δ) := by sorry

end HubSpokePricing.Lagrangian
