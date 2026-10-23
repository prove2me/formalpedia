-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_proposition_4_6
-- name    : HubSpokePricing.Lagrangian.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:35.944883+00:00
-- url     : https://prove2.me/theorems/744bcfeb-9ec3-462a-a6ba-f2d40a9912c2
-- title:
--   Proposition 4.6, p. 21 — under Assumption 4.1, ℙ[X̃₀(δ) ≤ 0] ≤ exp(−(b/2)·δ²/(m + n)) with b = 1/(1 + c)
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $0\le\delta<m$, $\lambda^*(\delta)$ optimal to (11), and $p_i$ ($i\in[n]$) optimal solutions of (6) at $\lambda^*(\delta)$, so that $\prod_ip_i(x_i)$ is the stationary law of the relaxed system under $\pi(\delta)$. Suppose **Assumption 4.1** holds at this $\delta$: $\mathbb E[\tilde X_i(\delta)]=\sum_x x\,p_i(x)\le c$ for all spokes $i$, for a constant $c>0$. Then with $b=1/(1+c)$,
--   $$\mathbb P\big[\tilde X_0(\delta)\le0\big]\;\le\;\exp\Big(-\frac b2\cdot\frac{\delta^2}{m+n}\Big),$$
--   where $\tilde X_0(\delta)=m-\sum_i\tilde X_i(\delta)$.
--
--   The relaxed hub level has mean at least $\delta$ and fluctuations of order $\sqrt{m+n}$, so its depletion probability decays like a Gaussian tail in $\delta/\sqrt{m+n}$.
--
--   **Formalization Note** The paper's Assumption 4.1 asks $\mathbb E[\tilde X_i(\delta)]\le c$ for all $\delta\ge0$; here it is assumed only at the $\delta$ in use, which is all the proof uses (a weaker hypothesis). $\mathbb E[\tilde X_i(\delta)]=\sum_x x\,p_i(x)$ because the relaxed stationary law is $\prod_ip_i(x_i)$ (Corollary B.10).
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 21, Proposition 4.6, Assumption 4.1

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Proposition 4.6 (p. 21): under Assumption 4.1 (`𝔼[X̃ᵢ(δ)] ≤ c`, `c > 0`) and with
`b = 1/(1 + c)`, the depletion probability of the relaxed system satisfies
`ℙ[X̃₀(δ) ≤ 0] ≤ exp(−(b/2) δ²/(m + n))`. -/
theorem proposition_4_6 (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m)
    (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (c : ℝ) (hc : 0 < c) (hmean : ∀ i, spokeMean (sol i) ≤ c) :
    relaxDepletionProb N sol ≤
      Real.exp (-((1 / (1 + c)) / 2) * (δ ^ 2 / ((N.m : ℝ) + N.n))) := by sorry

end HubSpokePricing.Lagrangian
