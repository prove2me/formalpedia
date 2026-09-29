-- Prove2me | Theorems.Thm_LubyMIS_MonteCarlo_lemmaA
-- name    : LubyMIS.MonteCarlo.lemmaA
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:51:16.978325+00:00
-- url     : https://prove2.me/theorems/2a8e4cd8-e387-40cb-b323-5f87d4380976
-- title:
--   LEMMA A (Beame) — Pr[i ∈ N(I′)] ≥ [¼·min{sum(i), 1}]·(1 − 1/2n²) for Algorithm A
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph, let $n \ge 1$ with $|V'| \le n$ (the number of vertices of the input graph), and run one select step of Algorithm A on $G'$: each vertex draws an independent uniform priority $\pi(i) \in \{1, \dots, n^4\}$, and $I'$ is the set of vertices whose priority is strictly smaller than that of each of their neighbours. Then for every vertex $i$ with $d(i) \ge 1$,
--   $$\Pr_A\big[i \in N(I')\big] \;\ge\; \Big[\tfrac14 \min\{\mathrm{sum}(i), 1\}\Big] \cdot \Big(1 - \frac{1}{2n^2}\Big), \qquad \mathrm{sum}(i) = \sum_{j \in \mathrm{adj}(i)} \frac{1}{d(j)} .$$
--
--   Summed against the degrees, this bound yields part (1) of Theorem 1: a single round of Algorithm A eliminates in expectation at least $\frac18 |E'| - \frac1{16}$ edges.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1041, LEMMA A (Beame)

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- LEMMA A (Beame) (Luby 1986, §3.4, p. 1041). For Algorithm A and every vertex `i` with
`d(i) ≥ 1`, `Pr[i ∈ N(I′)] ≥ [¼ · min {sum(i), 1}] · (1 − 1/(2n²))`. -/
theorem lemmaA {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) (H : SimpleGraph V) [DecidableRel H.Adj] (i : V)
    (hi : 1 ≤ H.degree i) :
    probA n (fun π => i ∈ nbhd H (selectA H π)) ≥
      (1 / 4 * min (sumInv H i) 1) * (1 - 1 / (2 * (n : ℝ) ^ 2)) := by sorry

end LubyMIS.MonteCarlo
