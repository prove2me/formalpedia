-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_4_53
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_4_53
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:02:49.2145+00:00
-- url     : https://prove2.me/theorems/f3f1438e-6785-4197-9838-c186de658d2b
-- title:
--   Theorem 4.53 — strict repacking lower bound, exact limit and asymptotically optimal strategy
-- statement:
--   Fix an integer capacity $C\ge1$ and rate $\nu>0$. On the complete $K$-node network, let calls between every pair arrive as independent Poisson streams of rate $\nu$, with independent unit-mean exponential holding times. Calls may be divided and repacked over arbitrary routes. Let $L_\nu(K)$ be the minimum loss over all nonanticipating stationary admissible strategies. Define $(\bar s,\bar\alpha)$ by (4.52) and $\bar L_\nu$ by the single-link distribution (4.51), with $\bar L_\nu=0$ when the threshold is infinite. Then
--   $$L_\nu(K)>\bar L_\nu\quad(K\ge2),\qquad L_\nu(K)\longrightarrow\bar L_\nu.$$
--   The network trunk-reservation strategy with these parameters is asymptotically optimal: its loss also converges to $\bar L_\nu$. Its provisional admission rule uses the number of calls between the arriving pair, and actual admission requires the stated direct-plus-two-edge routing aim to be feasible.
--
--   This identifies both the exact large-network optimum and a strategy attaining it asymptotically. The optimum ranges over the full policy class, and includes the unbounded-threshold and critical-load regimes.
--
--   Differences from the source:
--   - encoding: minimum loss over nonanticipating stationary strategies → infimum over every admissible stationary randomized admission rule and its normalized generator-stationary law; reason: the finite-state memoryless network has a sufficient call-count state; stationary Markovization preserves stationary performance
--   - reading: network with K nodes → finite-network inequality for K≥2 and an unrestricted K→∞ limit; reason: at K=0,1 there are no offered calls, so a per-offered-call loss probability is undefined
--   - encoding: s̄+ᾱ as a supremum, including s̄=∞ → extended nonnegative supremum with canonical integer/fractional parts and L̄=0 at infinity; reason: preserves the unbounded and critical-load cases without a real supremum default
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp.360–362, Theorem 4.53, (4.51)–(4.55)

import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Repacking

open Filter Topology

namespace KellyLossNetworks.RevisedDual.Supplement

/-- Kelly (1991), Theorem 4.53, p.361, (4.54)–(4.55): strict finite-network bound, exact
limit, and asymptotic optimality of the specified threshold strategy.
**Formalization Note.** The optimum ranges over all stationary randomized admissible
policies on the full repacking state space. All simple paths and divisible flows are
allowed. The strategy conclusion refers to the exact threshold from (4.52), including an
infinite supremum and ν=ν*. K≥2 is the domain in which network loss (per offered call) is
defined; sequences at K=0,1 are irrelevant to the limit. No single-link optimality assertion
or routing success conclusion is assumed. The reversed slack inequalities in the proof
on p.361 are not used as premises. -/
theorem theorem_4_53 (C : ℕ) (hC : 1 ≤ C) (nu : ℝ) (hnu : 0 < nu) :
    (∀ K : ℕ, 2 ≤ K → lowerRepackLoss C nu < optimalRepackLoss C nu K) ∧
    Tendsto (optimalRepackLoss C nu) atTop (𝓝 (lowerRepackLoss C nu)) ∧
    Tendsto (canonicalRepackLoss C nu) atTop (𝓝 (lowerRepackLoss C nu)) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
