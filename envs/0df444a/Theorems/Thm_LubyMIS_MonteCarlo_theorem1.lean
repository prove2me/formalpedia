-- Prove2me | Theorems.Thm_LubyMIS_MonteCarlo_theorem1
-- name    : LubyMIS.MonteCarlo.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:53:15.811983+00:00
-- url     : https://prove2.me/theorems/9652f5b8-008a-4851-a33b-0b89a964313e
-- title:
--   THEOREM 1 — one round of Algorithm A (B) eliminates at least ⅛·|E′| − 1/16 (⅛·|E′|) edges in expectation
-- statement:
--   Let $G' = (V', E')$ be the current graph before the $k$-th execution of the body of the while loop of Luby's MIS algorithm, and let $n \ge 1$ be the number of vertices of the input graph, so $|V'| \le n$. Write $Y_k = |E'|$ and $Y_{k+1}$ for the number of edges after that execution, i.e. after removing $I' \cup N(I')$ where $I'$ is produced by the select step.
--
--   1. For Algorithm A (independent uniform priorities in $\{1, \dots, n^4\}$; $I'$ the strict local minima),
--   $$E\big[Y_k^A - Y_{k+1}^A\big] \;\ge\; \frac18\, Y_k^A - \frac1{16}.$$
--   2. For Algorithm B (independent coins with $\Pr[\mathrm{coin}(i) = 1] = 1/(2d(i))$, and $1$ if $d(i) = 0$; $I'$ the marked vertices whose marked neighbours all have smaller degree),
--   $$E\big[Y_k^B - Y_{k+1}^B\big] \;\ge\; \frac18\, Y_k^B.$$
--
--   Each round thus removes a constant fraction of the remaining edges in expectation, which is what makes the expected number of rounds of both algorithms $O(\log n)$.
--
--   **Formalization Note** The expectation is taken for a fixed current graph $G'$, i.e. conditionally on the history of the first $k - 1$ rounds, as in the paper's proof ("Let $G' = (V', E')$ be the graph before the $k$th execution"); the unconditional statement follows by averaging. $n$ is a parameter with $1 \le n$ and $|V'| \le n$, not $|V'|$ itself. Expectations are finite sums over the $(n^4)^{|V'|}$ priority vectors and the $2^{|V'|}$ coin vectors.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1040, §3.4, THEOREM 1 (1) and (2)

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- THEOREM 1 (Luby 1986, §3.4, p. 1040). For the current graph `H = G′` and `n ≥ max(1, |V′|)` the
number of vertices of the input graph, one execution of the loop body eliminates in expectation
(1) at least `⅛ · |E′| − 1/16` edges under Algorithm A, and
(2) at least `⅛ · |E′|` edges under Algorithm B. -/
theorem theorem1 {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) (H : SimpleGraph V) [DecidableRel H.Adj] :
    expA n (fun π => (eliminated H (selectA H π) : ℝ)) ≥
        1 / 8 * (H.edgeFinset.card : ℝ) - 1 / 16 ∧
      expB H (fun c => (eliminated H (selectB H c) : ℝ)) ≥ 1 / 8 * (H.edgeFinset.card : ℝ) := by sorry

end LubyMIS.MonteCarlo
