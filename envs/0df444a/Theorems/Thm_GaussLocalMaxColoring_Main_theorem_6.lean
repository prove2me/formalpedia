-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_theorem_6
-- name    : GaussLocalMaxColoring.Main.theorem_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:19:50.839618+00:00
-- url     : https://prove2.me/theorems/42923857-da2a-400a-b6c0-cb309dd3738a
-- title:
--   Theorem 6 — a randomized polynomial-time algorithm properly colors every 3-colorable $n$-vertex graph with $O(n^{0.1537})$ colors with probability $\ge1-n^{-C}$
-- statement:
--   For every fixed $C>0$ there are a randomized polynomial-time algorithm and a constant $K>0$ such that, on every 3-colorable graph $G$ on $n$ vertices, with probability at least $1-n^{-C}$ the algorithm properly colors $G$ with at most $K\cdot n^{0.1537}$ distinct colors. The algorithm is one coin-using program of the integer RAM `CongruencyTU` with polynomial cost and register bit-length bounds, fixed before the input (given as its adjacency matrix); the probability is the fraction of coin strings yielding a proper coloring, at least $1-1/\lceil n^C\rceil\ge1-n^{-C}$; a coloring is a list of $n$ integer labels, adjacent vertices getting different labels, with at most $K n^{0.1537}$ distinct labels. The exponent is exactly $0.1537=1537/10000$; there is no degree restriction.
--
--   Differences from the source:
--   - encoding: "a randomized polynomial-time algorithm … with probability at least 1 − n^{−C}" (no machine model named) → CongruencyTU.RandSolves with nvars = ⌈n^C⌉₊ (success fraction ≥ 1 − 1/⌈n^C⌉ ≥ 1 − n^{−C}; probability 1 at n = 0) and Feasible = True; reason: the paper names no model; the published integer RAM with polynomial bit-length bounds; 1/⌈n^C⌉ ≤ n^{−C}
--   - encoding: O(n^{0.1537}) colors → ∃ K > 0 (after C, before the input) with at most K·n^{1537/10000} distinct labels for every n; reason: O(·) with an explicit constant; small n is absorbed by K
--   - encoding: a 3-colorable n-vertex graph; a proper coloring → Graph3 (Fin n, adjacency-matrix encoding) with G.Colorable 3; GoodColoring (n labels, adjacent labels differ, distinct labels counted); reason: the published graph layer
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Theorem 6, printed p. 5 (PDF 7)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_RecGaussColoring_Main_Graph

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Theorem 6** (p. 5, PDF 7). For every fixed `C > 0` there are a randomized polynomial-time
algorithm (one coin-using program of the integer RAM `CongruencyTU` with polynomial cost and
register bit-length bounds, fixed before the input) and a constant `K > 0` such that on every
3-colorable graph `G` on `n` vertices (adjacency matrix input), at least a `1 − 1/⌈n^C⌉ ≥ 1 − n^{−C}`
fraction of the coin strings yield a proper coloring of `G` with at most `K · n^{0.1537}`
distinct colors. -/
theorem theorem_6 (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧
      CongruencyTU.RandSolves encGraph graphSize ThreeColorable
        (fun I => ⌈(I.n : ℝ) ^ C⌉₊) (fun _ => True)
        (fun I out => GoodColoring I out (K * (I.n : ℝ) ^ (1537 / 10000 : ℝ))) := by sorry

end GaussLocalMaxColoring.Main
