-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_3
-- name    : HubSpokePricing.Lagrangian.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:35.899021+00:00
-- url     : https://prove2.me/theorems/91317e30-1a36-4f78-9a83-cbb6ca0671e9
-- title:
--   Proposition 3.3, p. 14 — d_i(x, i, 0) is increasing and d_i(x, 0, i) decreasing in x on the support I_i
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $\lambda\ge0$, let $i$ be a spoke, and let $p_i(x),d_i(x,i,0),d_i(x,0,i)$, $x\in[0:m]$, be an optimal solution of the spoke problem (6), with support $I_i=\{x:p_i(x)>0\}$. Then for all $x\le y$ in $I_i$,
--   $$d_i(x,i,0)\le d_i(y,i,0)\qquad\text{and}\qquad d_i(y,0,i)\le d_i(x,0,i).$$
--
--   The more resources spoke $i$ holds, the more readily the Lagrangian policy lets a resource leave it and the less readily it brings one in. This monotonicity drives the log-concavity of $p_i$ (Proposition B.9) and the bound of Lemma A.10.
--
--   **Formalization Note** "Increasing" and "decreasing" are read in the weak sense (the paper's Figure 2 shows flat stretches).
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 14, Proposition 3.3

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Proposition 3.3 (p. 14): for an optimal solution of (6), the control `d_i(x, i, 0)` is
increasing and `d_i(x, 0, i)` is decreasing in `x` on the support `I_i = {x : p_i(x) > 0}`. -/
theorem proposition_3_3 (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (i : Fin N.n) (s : SpokeSol N.m) (hs : SpokeOptimal N lam i s)
    (x y : Fin (N.m + 1)) (hxy : x ≤ y) (hx : 0 < s.p x) (hy : 0 < s.p y) :
    s.dOut x ≤ s.dOut y ∧ s.dIn y ≤ s.dIn x := by sorry

end HubSpokePricing.Lagrangian
