-- Prove2me | Theorems.Thm_KServer_competitive_of_covering_config
-- name    : KServer.competitive_of_covering_config
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:34:43.352093+00:00
-- url     : https://prove2.me/theorems/b349550e-a4c3-4ad8-a7c9-d7f4291a356d
-- title:
--   A configuration covering the whole space makes every competitive ratio achievable
-- statement:
--   Let $M$ be a metric space, $k\ge0$, and suppose some configuration $Y$ places a server on every point of $M$ — which happens exactly when $M$ has at most $k$ points.
--
--   **Statement.** For every $c\ge0$ and every initial configuration $C_0$ there is an online algorithm starting at $C_0$ that is $c$-competitive.
--
--   **Role.** This is the degenerate regime of the $k$-server problem, the one the classical theory excludes by assuming the metric space has at least $k$ points. With more servers than points there is nothing to decide: move to $Y$ on the first request and stay there for ever. Every subsequent request is already served, so the algorithm's total cost is $d(C_0,Y)$, a constant independent of the request sequence, and the competitiveness inequality
--   $$\mathrm{cost}_A(\sigma)\;\le\;c\cdot\mathrm{OPT}(C_0,\sigma)+d(C_0,Y)$$
--   holds for any $c\ge0$, using only that the optimum is nonnegative.
--
--   Together with `KServer.injective_or_covering` this disposes of the degenerate case in any theorem stated for an arbitrary metric space, leaving the substance of the argument to the regime where injective configurations exist.
--
--   **Formalization Note** The algorithm is `fun l => if l = [] then C₀ else Y`, which reports $C_0$ on the empty request list as required and $Y$ thereafter. Its cost telescopes to a single nonzero term, the first, isolated by bounding the $t$-th summand by `if t = 0 then moveCost C₀ Y else 0` and evaluating that sum with `Finset.sum_ite_eq'`; this handles the empty request sequence without a separate case. Nonnegativity of `offlineCost`, needed to absorb the factor $c$, is `Real.sInf_nonneg`, which also covers the vacuous case where the set of schedules is empty.
-- source:
--   Degenerate case of the k-server problem, excluded by the standing assumption that the metric space has at least k points in E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 1.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem competitive_of_covering_config (k : ℕ) (M : Type) [MetricSpace M] (C₀ Y : Config k M)
    (hY : ∀ x : M, ∃ i, Y i = x) (c : ℝ) (hc : 0 ≤ c) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A c := by sorry

end KServer
