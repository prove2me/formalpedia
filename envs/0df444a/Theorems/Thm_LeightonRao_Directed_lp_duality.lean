-- Prove2me | Theorems.Thm_LeightonRao_Directed_lp_duality
-- name    : LeightonRao.Directed.lp_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:19.251547+00:00
-- url     : https://prove2.me/theorems/b87b1fb1-53de-4574-a493-da2621ccef3b
-- title:
--   §2.2, p. 796, directed analogue (§2.4) — LP duality: an optimal distance function has total weight W = f
-- statement:
--   Let $G$ be a strongly connected directed network on $n\ge2$ nodes, and let $f$ be the max-flow of its directed uniform multicommodity flow problem. Then:
--
--   1. every nonnegative distance function $d$ satisfying the directed distance constraint $\sum_{(u,v)\in V^2}d(u,v)\ge1$ has total weight $W=\sum_{u,v}C(u,v)d(u,v)\ge f$; and
--   2. some nonnegative distance function $d$ satisfying the distance constraint has
--   $$W=f.$$
--
--   This is the linear programming duality between the concurrent flow LP and its dual (the distance LP). It reduces the lower bound of Theorem 12 to Lemma 16: a cut of small ratio cost is found from an optimal dual solution.
--
--   **Formalization Note** The paper states this duality in §2.2 for undirected UMFPs and uses its directed analogue in §2.4 ("The proof of Theorem 12 follows immediately from Lemma 16") without restating it. Strong connectivity and $n\ge2$ make the shortest-path distances well defined and the max-flow finite and positive.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 796, §2.2, LP duality sentence; directed analogue used in §2.4, p. 807

import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, §2.2 p. 796, directed analogue used in §2.4: every nonnegative distance function
satisfying the directed distance constraint has total weight at least the max-flow, and some such
distance function has total weight exactly the max-flow. -/
theorem lp_duality {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N) :
    (∀ d : V → V → ℝ, (∀ u v, 0 ≤ d u v) → SatisfiesDiConstraint N d →
        diMaxFlow N diDemand ≤ diTotalWeight N d) ∧
    (∃ d : V → V → ℝ, (∀ u v, 0 ≤ d u v) ∧ SatisfiesDiConstraint N d ∧
        diTotalWeight N d = diMaxFlow N diDemand) := by sorry

end LeightonRao.Directed
