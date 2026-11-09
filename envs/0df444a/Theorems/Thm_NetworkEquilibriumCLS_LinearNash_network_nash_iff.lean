-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_network_nash_iff
-- name    : NetworkEquilibriumCLS.LinearNash.network_nash_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:51.46595+00:00
-- url     : https://prove2.me/theorems/cc1899c9-5e3d-45ac-b388-94503b24445c
-- title:
--   Linear games — Definition 2.6 equals all-lottery Nash
-- statement:
--   Let G be any valid finite linear network congestion game and let σ assign a real weight to every feasible path of every player. Let u_i be minus the path cost, with expected payoff under the product of the players' weights. Then
--
--   $$\sigma\text{ satisfies Definition 2.6}\quad\Longleftrightarrow\quad\sigma\text{ is a mixed Nash profile for }u.$$
--
--   Both sides require actual nonnegative lotteries summing to one. On the left every feasible pure path is a deviation; on the right every lottery over all feasible paths is allowed. This supporting bridge makes the imported general game convention explicit without restricting the underlying path strategies.
--
--   Differences from the source:
--   - encoding: cost minimization and pure-path deviations → negative-cost payoff maximization and arbitrary lottery deviations; reason: expectation is linear in a unilateral lottery; this item asserts the equivalence as a proof obligation rather than assuming it
--   - generalization: directed graph input → distinct parallel edges are permitted in the network carrier; reason: ordinary directed graphs embed directly, and subdividing each parallel edge preserves all simple path choices and homogeneous costs with polynomial overhead
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), pp.7–8 (PDF 8–9), §2.3, Definition 2.6; standard linearity equivalence for finite mixed strategies, needed for the published AGT game interface.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Games

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem network_nash_iff :
    ∀ (G : Network), NetworkValid G → ∀ σ : ∀ i, PathAction G i → ℝ,
    NetworkNash G σ ↔ AGT.IsMixedNash (networkPayoff G) σ := by sorry

end NetworkEquilibriumCLS.LinearNash
