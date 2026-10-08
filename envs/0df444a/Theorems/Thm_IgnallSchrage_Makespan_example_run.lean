-- Prove2me | Theorems.Thm_IgnallSchrage_Makespan_example_run
-- name    : IgnallSchrage.Makespan.example_run
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:31:40.881464+00:00
-- url     : https://prove2.me/theorems/90785c35-96df-460d-a2d7-9bbf493427b5
-- title:
--   pp. 402–403, An Example — the 4-job run stops with node 231 first, and 2-3-1-4 is optimal with makespan 62
-- statement:
--   Consider the 4-job, 3-machine jobset of the paper:
--
--   | job | 1 | 2 | 3 | 4 |
--   |---|---|---|---|---|
--   | $a_i$ | 13 | 7 | 26 | 2 |
--   | $b_i$ | 3 | 12 | 9 | 6 |
--   | $c_i$ | 12 | 16 | 7 | 1 |
--
--   Run the branch-and-bound procedure with the bound $LB$ of p. 401 and the tie rule of p. 403. Then
--
--   1. after each of the first $6$ steps the first node of the list is not terminal;
--   2. after $6$ steps the first node is node $231$ (jobs $2,3,1$ in this order);
--   3. $LB(231)=62$;
--   4. the full sequence $2314$ (the one sequence beginning with $231$) has makespan $62$;
--   5. every one of the $24$ sequences has makespan at least $62$, so $2314$ is optimal.
--
--   In the paper's words, "node 231's lower bound, which is the makespan for sequence 2314, is less than or equal to the lower bound of any other 'unbranched from' node", "so 231 is optimal".
--
--   **Formalization Note** Jobs are numbered from $0$, so the paper's job $i$ is $i-1$ and node $231$ is the list $[1,2,0]$. The nodes branched are, in order, the root, $2$, $21$, $1$, $12$, $23$. The TIMEB/TIMEC columns of the paper's LIST table are not formalized.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), pp. 402–403, An Example (jobset, tree, LIST, "231 is optimal")

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure

namespace IgnallSchrage.Makespan

/-- pp. 402–403, the example: for the 4-job jobset `a = (13, 7, 26, 2)`, `b = (3, 12, 9, 6)`,
`c = (12, 16, 7, 1)` (jobs `1, 2, 3, 4` of the paper are `0, 1, 2, 3` here), the run first has
a terminal node first on the list after 6 steps, that node is `231` (`[1, 2, 0]`), its lower
bound is `62`, the full sequence `2314` (the one sequence beginning with `[1, 2, 0]`) has
makespan `62`, and no sequence has makespan below `62`; so `2314` is optimal. -/
theorem example_run (a b c : Fin 4 → ℝ) (ha : a = ![13, 7, 26, 2]) (hb : b = ![3, 12, 9, 6])
    (hc : c = ![12, 16, 7, 1]) :
    (∀ k < 6, ∀ P, (run (lowerBound a b c) k).head? = some P → ¬ IsTerminal P) ∧
    (run (lowerBound a b c) 6).head? = some [1, 2, 0] ∧
    lowerBound a b c [1, 2, 0] = 62 ∧
    (∀ σ : Equiv.Perm (Fin 4), BeginsWith σ [1, 2, 0] → makespan a b c σ = 62) ∧
    ∀ σ : Equiv.Perm (Fin 4), 62 ≤ makespan a b c σ := by sorry

end IgnallSchrage.Makespan
