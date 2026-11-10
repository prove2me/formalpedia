-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_optimal_point_count_ratio
-- name    : OnlineTransportation1195.Main.optimal_point_count_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:36:01.295514+00:00
-- url     : https://prove2.me/theorems/a9ba777c-6a81-4d18-a76c-451d4be9e9ef
-- title:
--   Theorem 1.2 — optimal point-count competitive ratio, both clauses
-- statement:
--   For every $n\ge2$, every $n$-point real metric with distinct garages and arbitrary natural capacities admits one deterministic causal policy satisfying, for all arrival sequences,
--
--   $$\operatorname{cost}_A\le(2n-3)\operatorname{OPT}.$$
--
--   Moreover, for every real factor $\rho<2n-3$, such a guarantee on all $n$-point instances is impossible. Equivalently, whatever causal policies are selected for the static instances, some instance and arrival sequence violate that smaller factor. The adversary's sequence is chosen after the policy, rather than letting a policy depend on the future. Both the upper bound and optimality are included, also at $n=2$.
--
--   Differences from the source:
--   - encoding: capacitated garage assignments and immediate irrevocable deterministic decisions → Fin n metric points, zero-based arrival times, slot permutations and a full-sequence function with equal-prefix garage causality; reason: all k cars fill all slots; slot labels carry no cost and causality gives a single feasible online rule on every sequence
--   - encoding: competitive ratio for the complete online problem → a nonnegative multiplicative factor and no division by OPT; reason: competitive factors have their conventional nonnegative domain; the inequality also states the zero-OPT case
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Theorem 1.2, PDF / printed p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_OnlinePolicy

namespace OnlineTransportation1195.Main

theorem optimal_point_count_ratio (n : ℕ) (hn : 2 ≤ n) :
    PointRatio n (2 * (n : ℝ) - 3) ∧
      ∀ ρ : ℝ, ρ < 2 * (n : ℝ) - 3 → ¬ PointRatio n ρ := by sorry

end OnlineTransportation1195.Main
