-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_bounded_reach_ball_card
-- name    : KSATSingleFlip.Connect.bounded_reach_ball_card
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:26:10.164596+00:00
-- url     : https://prove2.me/theorems/c8c9ed2a-0003-474f-8781-a88260b8550e
-- title:
--   Geometric bound for a bounded-branching reachability ball
-- statement:
--   In any directed graph represented by finite outgoing-neighbor sets of size at most $d$, the set of vertices reachable from a root in at most $r$ steps has cardinality at most $\sum_{i=0}^{r}d^i$. No finiteness assumption on the ambient vertex type is required.
-- source:
--   Auxiliary path-counting bound for Lemma 2.7 in Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_BoundedReach

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- A degree-d finite reachability ball has at most a geometric number of vertices. -/
theorem bounded_reach_ball_card {V : Type} [DecidableEq V] (neighbors : V → Finset V)
    (root : V) (d r : ℕ) (hd : ∀ u, (neighbors u).card ≤ d) :
    (boundedReachBall neighbors root r).card ≤ ∑ i ∈ Finset.range (r + 1), d^i := by
  sorry

end KSATSingleFlip.Connect
