-- Prove2me | Theorems.Thm_MulticlassQNet_SingleStation_Supplement_theorem_6_1_closed_polyhedron
-- name    : MulticlassQNet.SingleStation.Supplement.theorem_6_1_closed_polyhedron
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:31:51.908691+00:00
-- url     : https://prove2.me/theorems/3409a1b1-d220-423b-9252-9a6afd3caf2a
-- title:
--   Theorem 6.1 — the achievable (n, I, u) of a closed network lies in the polyhedron (43)–(47) (corrected: summation index of (47))
-- statement:
--   Consider a closed multiclass network (§6): $N$ single-server stations, $R$ classes, fixed routing probabilities $p_{rs}$ with $\sum_sp_{rs}=1$ (no exits), no external arrivals, exponential service rates $\mu_r>0$, and $F$ customers always present. For a Markovian sequencing policy (idling and preemption allowed) satisfying Assumption A(a) on the population-$F$ states, let $n_r=E[n_r]$, $u_r=E[1\{B_r\}]$ and $I_{rr'}=E[1\{B_r\}n_{r'}]$ under its invariant distribution. Then
--
--   $$\mu_ru_r-\sum_{l=1}^R\mu_lu_lp_{lr}=0,\qquad r=1,\dots,R,\qquad(43)$$
--
--   $$2\mu_rI_{rr}-2\sum_{l=1}^R\mu_lp_{lr}I_{lr}=u_r\mu_r(1-p_{rr})+\sum_{l\ne r}\mu_lu_lp_{lr},\qquad r=1,\dots,R,\qquad(44)$$
--
--   $$\mu_rI_{rr'}+\mu_{r'}I_{r'r}-\sum_{w=1}^R\mu_wp_{wr}I_{wr'}-\sum_{w=1}^R\mu_wp_{wr'}I_{wr}=-\mu_ru_rp_{rr'}-\mu_{r'}u_{r'}p_{r'r},\qquad r>r',\qquad(45)$$
--
--   $$\sum_{l\in C_i}I_{lr}\le n_r,\ \ r=1,\dots,R,\ i=1,\dots,N,\qquad(46)\qquad\qquad\sum_{l=1}^Rn_l=F,\qquad(47)$$
--
--   and $n_r,I_{rr'},u_r\ge0$.
--
--   Maximizing the weighted throughput $\sum_rc_r\mu_ru_r$ over this polyhedron gives an upper bound on the optimal weighted throughput of the closed network.
--
--   **Formalization Note** The closed network is the published network record with the hypotheses $\lambda_{0r}=0$ and $\sum_sp_{rs}=1$ for every $r$; policies, $u_r$ (`busyProb`), $I_{rr'}$ (`busyMoment`) and $n_r$ (`meanNum`) are the published ones. Assumption A(a) is `ClosedAssumptionA`: invariance, support on $\{\sum_rn_r=F\}$, and uniqueness among invariant distributions with that support.
--
--   Differences from the source:
--   - reading: "the Markov chain has a unique invariant distribution" (A(a)) → Lean asks uniqueness among invariant distributions living on the population-$F$ states; reason: the closed chain's state space is $\{\sum_rn_r=F\}$ (p. 24), and the chain on $\mathbb N^R$ has one invariant law per population level, so global uniqueness could never hold
--   - correction: (47) is printed $\sum_{l=1}^Rn_r=F$ → Lean has $\sum_ln_l=F$; reason: summation-index typo; the proof says (47) expresses that there are $F$ customers in the closed network
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 25, Theorem 6.1, Eqs. (43)–(47); setting pp. 24–25, §6; proof p. 26

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_Closed

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 6.1 (p. 25): in a closed network (no external arrivals, no exits) with `F`
customers, for every sequencing policy satisfying Assumption A(a) on the population-`F` states,
`n_r = E[n_r]`, `u_r = E[1{B_r}]` and `I_{rr'} = E[1{B_r} n_{r'}]` satisfy (43)–(47) and are
nonnegative. -/
theorem theorem_6_1_closed_polyhedron {N R : ℕ} (net : Network N R)
    (hnoarr : ∀ r, net.lam0 r = 0) (hnoexit : ∀ r, ∑ s, net.p r s = 1) (F : ℕ)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : ClosedAssumptionA P F π) :
    -- (43)
    (∀ r, net.μ r * P.busyProb π r - ∑ l, net.μ l * P.busyProb π l * net.p l r = 0) ∧
    -- (44)
    (∀ r, 2 * net.μ r * P.busyMoment π r r - 2 * ∑ l, net.μ l * net.p l r * P.busyMoment π l r
      = P.busyProb π r * net.μ r * (1 - net.p r r)
        + ∑ l ∈ Finset.univ.erase r, net.μ l * P.busyProb π l * net.p l r) ∧
    -- (45)
    (∀ r r', r' < r →
      net.μ r * P.busyMoment π r r' + net.μ r' * P.busyMoment π r' r
        - ∑ w, net.μ w * net.p w r * P.busyMoment π w r'
        - ∑ w, net.μ w * net.p w r' * P.busyMoment π w r
      = -(net.μ r * P.busyProb π r * net.p r r') - net.μ r' * P.busyProb π r' * net.p r' r) ∧
    -- (46)
    (∀ i r, ∑ l ∈ net.C i, P.busyMoment π l r ≤ meanNum π r) ∧
    -- (47)
    (∑ l, meanNum π l = F) ∧
    -- nonnegativity
    (∀ r, 0 ≤ meanNum π r) ∧ (∀ r r', 0 ≤ P.busyMoment π r r') ∧
    (∀ r, 0 ≤ P.busyProb π r) := by sorry

end MulticlassQNet.SingleStation.Supplement
