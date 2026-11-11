-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_theorem_5
-- name    : GaussLocalMaxColoring.Main.theorem_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:24:33.50937+00:00
-- url     : https://prove2.me/theorems/6aa36123-52e5-4e30-a514-32d2b27cebf9
-- title:
--   Theorem 5 — for $\beta=0.692601$, an independent set of size $n^{(1+\beta)/2-o(1)}$ in 3-colorable graphs with $\Delta\le n^\beta$, with probability $\ge1-n^{-C}$
-- statement:
--   Let $\beta=0.692601$. For every fixed $C>0$ there are a randomized polynomial-time algorithm and one function $g(n)\to0$ such that, on every 3-colorable graph $G$ on $n$ vertices with maximum degree at most $n^\beta$, with probability at least $1-n^{-C}$ it returns an independent set $I$ with $|I|\ge n^{(1+\beta)/2-g(n)}$. The algorithm is one coin-using program of the integer RAM `CongruencyTU` with polynomial cost and register bit-length bounds fixed before the input; the probability is the fraction of good coin strings, at least $1-1/\lceil n^C\rceil\ge1-n^{-C}$; the input is the adjacency matrix and the output the characteristic vector of $I$.
--
--   Differences from the source:
--   - encoding: "a randomized polynomial-time algorithm … with probability at least 1 − n^{−C}" (no machine model named) → CongruencyTU.RandSolves with nvars = ⌈n^C⌉₊ (success fraction ≥ 1 − 1/⌈n^C⌉ ≥ 1 − n^{−C}) and Feasible = True; reason: the paper names no model; the published integer RAM with polynomial bit-length bounds; 1/⌈n^C⌉ ≤ n^{−C} so the Lean demand is at least the source's
--   - encoding: graph input and returned set → Graph3 with the adjacency-matrix encoding; output a characteristic vector (DecodesSet); reason: machine input/output layout
--   - reading: o(1) in the exponent → one function g → 0 chosen after C and before the input; reason: the paper's uniform asymptotic convention
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Theorem 5, printed p. 4 (PDF 6); proof p. 52 (PDF 54)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_GaussLocalMaxColoring_Main_Machine

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Theorem 5** (p. 4, PDF 6; proved p. 52, PDF 54). Let `β = 0.692601`. For every fixed
`C > 0` there are a randomized polynomial-time algorithm (one coin-using `CongruencyTU` program
with polynomial cost and bit-length bounds) and one function `g → 0` such that, on every
3-colorable graph on `n` vertices with maximum degree at most `n^β`, with probability at least
`1 − 1/⌈n^C⌉ ≥ 1 − n^{−C}` over the coins it returns an independent set `I` with
`|I| ≥ n^{(1+β)/2 − g(n)}`. -/
theorem theorem_5 (C : ℝ) (hC : 0 < C) :
    ∃ g : ℕ → ℝ, IsLittleO1 g ∧
      CongruencyTU.RandSolves encGraph graphSize (ThreeColDegLe beta5)
        (fun I => ⌈(I.n : ℝ) ^ C⌉₊) (fun _ => True) (GoodIndepO ((1 + beta5) / 2) g) := by sorry

end GaussLocalMaxColoring.Main
