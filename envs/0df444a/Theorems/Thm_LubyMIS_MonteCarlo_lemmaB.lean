-- Prove2me | Theorems.Thm_LubyMIS_MonteCarlo_lemmaB
-- name    : LubyMIS.MonteCarlo.lemmaB
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:51:47.49072+00:00
-- url     : https://prove2.me/theorems/e63acc8b-44b0-43cf-9277-440b1f636156
-- title:
--   LEMMA B — Pr[i ∈ N(I′)] ≥ ¼·min{sum(i)/2, 1} for Algorithm B
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph and run one select step of Algorithm B on $G'$: each vertex $i$ independently puts itself into $X$ with probability $1/(2d(i))$ (with probability $1$ if $d(i) = 0$), and $I'$ consists of those $i \in X$ all of whose neighbours in $X$ have degree strictly smaller than $d(i)$. Then for every vertex $i$ with $d(i) \ge 1$,
--   $$\Pr_B\big[i \in N(I')\big] \;\ge\; \tfrac14 \min\Big\{\frac{\mathrm{sum}(i)}{2}, 1\Big\}, \qquad \mathrm{sum}(i) = \sum_{j \in \mathrm{adj}(i)} \frac{1}{d(j)} .$$
--
--   Summed against the degrees, this bound yields part (2) of Theorem 1: a single round of Algorithm B eliminates in expectation at least $\frac18 |E'|$ edges.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1042, LEMMA B

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- LEMMA B (Luby 1986, §3.4, p. 1042). For Algorithm B and every vertex `i` with `d(i) ≥ 1`,
`Pr[i ∈ N(I′)] ≥ ¼ · min {sum(i)/2, 1}`. -/
theorem lemmaB {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) (hi : 1 ≤ H.degree i) :
    probB H (fun c => i ∈ nbhd H (selectB H c)) ≥ 1 / 4 * min (sumInv H i / 2) 1 := by sorry

end LubyMIS.MonteCarlo
