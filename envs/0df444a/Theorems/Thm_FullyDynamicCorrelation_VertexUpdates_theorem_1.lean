-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_theorem_1
-- name    : FullyDynamicCorrelation.VertexUpdates.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:55:03.578171+00:00
-- url     : https://prove2.me/theorems/118bfad3-46e0-4cfa-abb2-97d169accf10
-- title:
--   Theorem 1 — constant-factor fully dynamic correlation clustering under vertex updates in polylog amortized time
-- statement:
--   There is $A\ge1$ such that for every horizon exponent $d\in\mathbb N$ and confidence exponent $c>0$ there are a program $P$ of the adjacency-list RAM, $B>0$ and $k\in\mathbb N$ with the following property. For every $n\ge2$, every valid stream of $m\le n^d$ vertex insertions and deletions fixed in advance (starting from the empty graph, vertex names $<n$), and every adjacency-list presentation of the graphs it produces, with probability at least $1-n^{-c}$ the run of $P$ processes all $m$ updates within $\lfloor B\,m\,(1+\log_2n)^k\rfloor$ instructions in total, and at every returned time $t$ the clustering given by the label cells has cost at most $A\cdot\mathrm{opt}(G^{(t)})$.
--
--   Differences from the source:
--   - encoding: a randomized fully dynamic vertex-update algorithm in the adjacency-list model → a Program of the unit-cost adjacency-list RAM (RAM module); each update’s kind and vertex are written to cells 0–1 and n to cell 2, the program runs to halting and keeps its memory; reason: the paper’s model (Definitions 1–2): O(1) queries, adjacency lists maintained outside the algorithm at no cost; no multiplication or division, so no stronger than the paper’s machine
--   - encoding: maintains a clustering → the clustering read from the label cells of the active vertices at the end of each update (labelRel); reason: the algorithm stores labels; reading them is not charged, changing them is
--   - encoding: vertices and the bound n → names in {0, …, n−1}, at most n present at a time, names reusable after deletion; n ≥ 2; reason: Table 1: n bounds the number of vertices present; n ≥ 2 only excludes graphs on which every clustering is optimal
--   - reading: a sequence of poly(|V|) worst-case updates → for every fixed exponent d, every valid stream of length m ≤ n^d fixed in advance, with every presentation order of the adjacency lists; reason: the paper’s regime m = poly(n) (p. 13) with the oblivious adversary of Definition 2
--   - reading: O(1)-approximation “with high probability” and polylog(n) amortized update time → one universal A ≥ 1; for every d and c > 0, constants B, k and a program such that, with probability ≥ 1 − n^(−c), all returned clusterings satisfy cost ≤ A · opt and the total number of instructions is ≤ B m (1 + log₂ n)^k, on one event; reason: the amplification of p. 18 and the union bound of p. 63 give any inverse-polynomial failure; correctness and time hold together
--   - encoding: correlation clustering cost and opt → cost and opt of the Graph module (opt the attained minimum over partitions of the current vertex set); reason: Problem 1; the bound is multiplicative also when opt = 0
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Theorem 1, p. 3; amplification pp. 18, 63, 71

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_RAM

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Theorem 1 (p. 3). -/
theorem theorem_1 :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (d : ℕ) (c : ℝ), 0 < c →
        ∃ (P : Program) (B : ℝ) (k : ℕ), 0 < B ∧
          ∀ n : ℕ, 2 ≤ n →
            ∀ us : List Update, ValidStream n us → us.length ≤ n ^ d →
              ∀ adj : ℕ → ℕ → List ℕ, (∀ t, Presents (graphAt us (t + 1)) (adj t)) →
                1 - (n : ℝ) ^ (-c) ≤
                  ((execStream P n us adj ⌊B * (us.length : ℝ) * (1 + lg n) ^ k⌋₊).toOuterMeasure
                    {o | ∃ ms : List (ℕ → ℕ), o = some ms ∧
                      ∀ (t : ℕ) (ht : t < ms.length),
                        ((graphAt us (t + 1)).cost (labelRel (ms[t]'ht)) : ℝ) ≤
                          A * ((graphAt us (t + 1)).opt : ℝ)}).toReal := by sorry

end FullyDynamicCorrelation.VertexUpdates
