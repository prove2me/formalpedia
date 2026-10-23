-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_2
-- name    : HubSpokePricing.Lagrangian.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:23.245985+00:00
-- url     : https://prove2.me/theorems/b18a9dbb-e244-4e28-a265-630eb10b2be4
-- title:
--   Proposition 3.2, p. 12 — the optimal value h_i^λ of (6) solves the spoke Bellman equation (5)
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Fix $\lambda\ge0$ and a spoke $i$, and let $h_i^\lambda$ be the optimal value of the spoke problem (6). Then there are differential value functions $v_i^\lambda(x,i,0)$, $v_i^\lambda(x,0,i)$, $v_i^\lambda(x,\varnothing)$, $x\in[0:m]$, such that, with the average $v_i^\lambda(x)=q_{i0}v_i^\lambda(x,i,0)+q_{0i}v_i^\lambda(x,0,i)+(1-q_{i0}-q_{0i})v_i^\lambda(x,\varnothing)$, for every $x\in[0:m]$:
--   $$
--   \begin{aligned}
--   h_i^\lambda+v_i^\lambda(x,i,0)&=\max_{d\in[0,1\wedge x]}\big\{r_{i0}(d)+d\,(v_i^\lambda(x-1)-v_i^\lambda(x))\big\}+v_i^\lambda(x)-\lambda x,\\
--   h_i^\lambda+v_i^\lambda(x,0,i)&=\max_{d\in[0,1\wedge(m-x)]}\big\{r_{0i}(d)+d\,(v_i^\lambda(x+1)-v_i^\lambda(x))\big\}+v_i^\lambda(x)-\lambda x,\\
--   h_i^\lambda+v_i^\lambda(x,\varnothing)&=v_i^\lambda(x)-\lambda x.
--   \end{aligned}
--   $$
--
--   These are the average-reward Bellman equations (5) of the spoke-$i$ dynamic program of the Lagrangian relaxation. The statement says that the stationary-distribution problem (6) gives the spoke DP's optimal average revenue, which is what Proposition 3.2 asserts.
--
--   **Formalization Note** In this mission $h_i^\lambda$ is *defined* as the optimal value of (6), so Proposition 3.2 is stated as: that value solves (5). Value functions are taken on $\mathbb N$ and only evaluated at levels in $[0:m]$; at $x=0$ (resp. $x=m$) the maximization range is $\{0\}$, so the truncated $x-1$ (resp. $x+1=m+1$) does not matter. The maxima are written as suprema over the compact interval.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 12, Proposition 3.2, (6); p. 12, (5) of Proposition 3.1

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Proposition 3.2 (p. 12), stated through the spoke Bellman equation (5) of Proposition 3.1:
the optimal value `h_i^λ` of problem (6), together with some differential value functions
`v_i^λ(x, i, 0)`, `v_i^λ(x, 0, i)`, `v_i^λ(x, ∅)`, solves (5) for every level `x ∈ [0 : m]`. -/
theorem proposition_3_2 (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (i : Fin N.n) :
    ∃ vOut vIn vNone : ℕ → ℝ,
      ∀ x : ℕ, x ≤ N.m →
        h N lam i + vOut x =
            (⨆ d : Set.Icc (0 : ℝ) (min 1 (x : ℝ)),
              N.rOut i d + d * ((N.qOut i * vOut (x - 1) + N.qIn i * vIn (x - 1) +
                  (1 - (N.qOut i + N.qIn i)) * vNone (x - 1)) -
                (N.qOut i * vOut x + N.qIn i * vIn x + (1 - (N.qOut i + N.qIn i)) * vNone x))) +
            (N.qOut i * vOut x + N.qIn i * vIn x + (1 - (N.qOut i + N.qIn i)) * vNone x) -
            lam * x ∧
        h N lam i + vIn x =
            (⨆ d : Set.Icc (0 : ℝ) (min 1 ((N.m : ℝ) - x)),
              N.rIn i d + d * ((N.qOut i * vOut (x + 1) + N.qIn i * vIn (x + 1) +
                  (1 - (N.qOut i + N.qIn i)) * vNone (x + 1)) -
                (N.qOut i * vOut x + N.qIn i * vIn x + (1 - (N.qOut i + N.qIn i)) * vNone x))) +
            (N.qOut i * vOut x + N.qIn i * vIn x + (1 - (N.qOut i + N.qIn i)) * vNone x) -
            lam * x ∧
        h N lam i + vNone x =
            (N.qOut i * vOut x + N.qIn i * vIn x + (1 - (N.qOut i + N.qIn i)) * vNone x) -
            lam * x := by sorry

end HubSpokePricing.Lagrangian
