-- Prove2me | Theorems.Thm_NonmonotoneSubmod_QueryLB_balanced_queries_indistinguishable
-- name    : NonmonotoneSubmod.QueryLB.balanced_queries_indistinguishable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:16:54.476764+00:00
-- url     : https://prove2.me/theorems/a267331e-2de8-404b-a1d6-11526b592ea8
-- title:
--   §4.2 — balanced queries cannot distinguish $f_C$ from the cut function $g$
-- statement:
--   Let $A$ be a deterministic adaptive algorithm making $q$ value queries on $[n]$, let $C \subseteq [n]$, and let $g(S) = |S|(n-|S|)$. Suppose that every query $Q_1, \dots, Q_q$ that $A$ issues when run against the oracle $g$ is balanced for $(C, [n]\setminus C)$. Then, run against $f_C$ instead, $A$ receives the same answers after each of its first $i$ queries for every $i \le q$, and so issues the same queries and returns the same set:
--
--   $$
--   A(f_C) = A(g).
--   $$
--
--   This is the step "as long as queries are balanced, the algorithm gets the same answer regardless of $(C, D)$": the algorithm's whole computation path is determined by $g$.
--
--   **Formalization Note** No hypothesis on $n$, $m$ or $|C|$ is needed; the statement holds for every $C$ because $f_C$ and $g$ agree on balanced sets.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1150, §4.2, proof of Theorem 4.5, first paragraph

import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance
import Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm

namespace NonmonotoneSubmod.QueryLB

/-- §4.2, proof of Theorem 4.5 (p. 1150, first paragraph): if every query that a deterministic
`q`-query algorithm `A` issues against the cut oracle `g(S) = |S|(n − |S|)` is balanced for
`(C, Cᶜ)`, then `A` receives the same answers from `f_C` as from `g`, issues the same queries
and returns the same set. -/
theorem balanced_queries_indistinguishable (n m q : ℕ) (A : DetAlg (Fin n) q)
    (C : Finset (Fin n)) (hbal : ∀ i < q, Balanced n m C (A.queryAt (gCut n) i)) :
    (∀ i ≤ q, A.answers (fC n m C) i = A.answers (gCut n) i) ∧
      A.run (fC n m C) = A.run (gCut n) := by sorry

end NonmonotoneSubmod.QueryLB
