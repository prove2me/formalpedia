-- Prove2me | Theorems.Thm_IgnallSchrage_Makespan_node_counts
-- name    : IgnallSchrage.Makespan.node_counts
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:31:24.837454+00:00
-- url     : https://prove2.me/theorems/8b17b233-bcfe-4c71-8cec-3b017f8482e8
-- title:
--   p. 403 — at least $\frac12 n(n+1)$ and at most $1+n+n(n-1)+\cdots+n!$ nodes are created; at most $n!$ are on the list
-- statement:
--   Run the branch-and-bound procedure with the bound $LB$ of p. 401 on $n\ge1$ jobs with real processing times. Write $\mathrm{created}(k)$ for the number of nodes created in the first $k$ steps (the root included) and $\mathrm{run}(k)$ for the list after $k$ steps.
--
--   1. Whenever the first node of $\mathrm{run}(k)$ is terminal,
--   $$
--   \mathrm{created}(k)\ \ge\ \tfrac12\,n(n+1).
--   $$
--   2. For every $k$,
--   $$
--   \mathrm{created}(k)\ \le\ 1+n+n(n-1)+\cdots+\frac{n!}{1!} \;=\; \sum_{j=0}^{n-1}\frac{n!}{(n-j)!}.
--   $$
--   3. For every $k$, the list $\mathrm{run}(k)$ holds at most $n!$ nodes.
--
--   These are the paper's best and worst cases for the effort of the procedure. Part 2 says the procedure never creates a node twice, so it creates at most every node of the tree down to depth $n-1$; together with the fact that every non-terminal step creates at least one node, it also shows that the procedure stops.
--
--   **Formalization Note** The paper writes $1+n+n(n-1)+\cdots+n!$; its last term $n!=n!/1!$ is the number of nodes at depth $n-1$, the depth at which the procedure stops. The minimum is stated as $n(n+1)\le 2\,\mathrm{created}(k)$ to avoid natural-number division. The paper's "in this case, $\tfrac12 n(n-1)+1$ nodes will be on the list" for the minimal run is not formalized.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 403, An Example, "In general, a minimum of ½n(n+1) nodes must be created ... The worst possible case would require the creation of all 1+n+n(n−1)+⋯+n! nodes while having n! of them on the list"

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure

namespace IgnallSchrage.Makespan

/-- p. 403, node counts of the branch-and-bound run with the bound `LB` of p. 401, for
`n ≥ 1` jobs:
(a) whenever the first node of the list is terminal, at least `½ n (n+1)` nodes have been
created;
(b) at every stage at most `1 + n + n(n-1) + ⋯ + n!/1! = ∑_{k<n} n!/(n-k)!` nodes have been
created;
(c) at every stage the list holds at most `n!` nodes. -/
theorem node_counts {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ) :
    (∀ k P, (run (lowerBound a b c) k).head? = some P → IsTerminal P →
      n * (n + 1) ≤ 2 * createdCount (lowerBound a b c) k) ∧
    (∀ k, createdCount (lowerBound a b c) k ≤ ∑ j ∈ Finset.range n, n.descFactorial j) ∧
    (∀ k, (run (lowerBound a b c) k).length ≤ n.factorial) := by sorry

end IgnallSchrage.Makespan
