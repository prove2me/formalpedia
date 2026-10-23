-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_proposition_B_9
-- name    : HubSpokePricing.Lagrangian.proposition_B_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:30.877073+00:00
-- url     : https://prove2.me/theorems/a2feb646-7924-4bd8-9916-6d84c21ceddd
-- title:
--   Proposition B.9, p. 66 — the optimal spoke distribution p_i(x) of (6) is discrete log-concave
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $\lambda\ge0$, let $i$ be a spoke and let $p_i(x),d_i(x,i,0),d_i(x,0,i)$ be an optimal solution of the spoke problem (6). Extend $p_i$ by $p_i(x)=0$ for $x>m$. Then $p_i$ is discrete log-concave (Definition B.1): its support is a set of consecutive integers and
--   $$p_i(x)^2\;\ge\;p_i(x-1)\,p_i(x+1)\qquad\text{for all }x\ge1.$$
--
--   Log-concavity of each spoke's stationary distribution is what lets the depletion probability of the relaxed system be bounded through geometric-type moment bounds (Lemmas A.12, A.14).
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 66, Proposition B.9, Definition B.1

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model
import Definitions.Def_HubSpokePricing_Lagrangian_Prob

namespace HubSpokePricing.Lagrangian

/-- Proposition B.9 (p. 66): the stationary distribution `p_i(x)` of an optimal solution of (6)
(extended by `0` beyond `m`) is discrete log-concave. -/
theorem proposition_B_9 (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (i : Fin N.n) (s : SpokeSol N.m) (hs : SpokeOptimal N lam i s) :
    IsLogConcave s.pN := by sorry

end HubSpokePricing.Lagrangian
