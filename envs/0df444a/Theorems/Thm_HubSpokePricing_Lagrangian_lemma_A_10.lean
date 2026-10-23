-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_lemma_A_10
-- name    : HubSpokePricing.Lagrangian.lemma_A_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:27.592059+00:00
-- url     : https://prove2.me/theorems/f2e99b0a-63e3-4c83-bb7e-027c7c894554
-- title:
--   Lemma A.10, p. 48 — under the Lagrangian controls, Δv_{i,t}(x) = v_{i,t}(x) − v_{i,t}(x − 1) ≤ ω̄
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $\lambda\ge0$, let $i$ be a spoke and let the Lagrangian controls $d_i(x,i,0),d_i(x,0,i)$ come from an optimal solution of (6) (Definition 3.1, with $d_i(x,i,0)=1$, $d_i(x,0,i)=0$ above the support). Define the finite-horizon values of spoke $i$ by $v_{i,0}\equiv0$ and, as in (35),
--   $$v_{i,t}(x)=q_{i0}\big[r_{i0}(d_i(x,i,0))+d_i(x,i,0)\,(v_{i,t-1}(x-1)-v_{i,t-1}(x))\big]+q_{0i}\big[r_{0i}(d_i(x,0,i))+d_i(x,0,i)\,(v_{i,t-1}(x+1)-v_{i,t-1}(x))\big]+v_{i,t-1}(x).$$
--   Then for every $t\ge0$ and every $x\in[m]=\{1,\dots,m\}$,
--   $$\Delta v_{i,t}(x)=v_{i,t}(x)-v_{i,t}(x-1)\;\le\;\bar\omega .$$
--
--   One more resource in a spoke is worth at most $\bar\omega$ in continuation value. This is the per-event loss bound $\bar r+\bar\omega$ in Lemma 4.3.
--
--   **Formalization Note** The recursion is (35) averaged over request types, without a Lagrangian penalty term, exactly as printed. The levels are natural numbers; the boundary terms at $x=0$ and $x=m$ carry the factors $d_i(0,i,0)=0$ and $d_i(m,0,i)=0$.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 48, Lemma A.10, (35)

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Lemma A.10 (p. 48): under the Lagrangian controls, the differences of the finite-horizon
continuation values `Δv_{i,t}(x) = v_{i,t}(x) − v_{i,t}(x − 1)` of (35) are at most `ω̄`, for all
`t` and `x ∈ [m]`. -/
theorem lemma_A_10 (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (i : Fin N.n) (s : SpokeSol N.m) (hs : SpokeOptimal N lam i s)
    (t x : ℕ) (hx1 : 1 ≤ x) (hxm : x ≤ N.m) :
    spokeValue N i s t x - spokeValue N i s t (x - 1) ≤ N.omega := by sorry

end HubSpokePricing.Lagrangian
