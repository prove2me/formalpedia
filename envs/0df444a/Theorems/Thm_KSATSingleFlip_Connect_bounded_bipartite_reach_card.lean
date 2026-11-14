-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_bounded_bipartite_reach_card
-- name    : KSATSingleFlip.Connect.bounded_bipartite_reach_card
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:26:11.07771+00:00
-- url     : https://prove2.me/theorems/6cf31eca-ed73-476c-afe4-80a792a9180f
-- title:
--   Bounded two-step reachability in a bipartite incidence system
-- statement:
--   In a finite-neighbor bipartite incidence system, suppose every variable has at most $D$ incident clauses and every clause has at most $k$ variables. Starting from one variable, at most $\sum_{i=0}^{r}(Dk)^i$ variables are reachable by at most $r$ variable–clause–variable steps. This provides a path-counting ingredient for the factor-ball bounds in Lemma 2.7.
-- source:
--   Auxiliary path-counting bound for Lemma 2.7 in Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_BoundedReach

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Two-step reachability in a bounded bipartite incidence system. -/
theorem bounded_bipartite_reach_card {V C : Type} [DecidableEq V] [DecidableEq C]
    (clauses : V → Finset C) (scope : C → Finset V)
    (root : V) (D k r : ℕ)
    (hD : ∀ v, (clauses v).card ≤ D) (hk : ∀ c, (scope c).card ≤ k) :
    (boundedReachBall (fun v => (clauses v).biUnion scope) root r).card ≤
      ∑ i ∈ Finset.range (r + 1), (D*k)^i := by
  sorry

end KSATSingleFlip.Connect
