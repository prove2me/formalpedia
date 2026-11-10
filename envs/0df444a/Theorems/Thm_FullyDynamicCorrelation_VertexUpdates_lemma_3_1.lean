-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_lemma_3_1
-- name    : FullyDynamicCorrelation.VertexUpdates.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:54:53.375096+00:00
-- url     : https://prove2.me/theorems/adae0c08-6a42-4b10-b21c-3797a161c813
-- title:
--   Lemma 3.1 — a gap sparsity tester in O(log² n/(α²ε²)) time
-- statement:
--   For every $c>0$ there is $C>0$ such that for all $\alpha,\varepsilon>0$ with $\alpha\varepsilon\le1/100$ there is a program which, on every graph with vertex names $<n$ ($n\ge2$), every adjacency-list presentation and every vertex $v$, with probability at least $1-n^{-c}$ halts within $\lfloor C\log_2^2n/(\alpha^2\varepsilon^2)\rfloor$ instructions and answers (cell $0$) *yes* ($1$) if $v$ is $\alpha\varepsilon$-sparse and *no* ($0$) if $v$ is not $(1-\eta)\alpha\varepsilon$-sparse, $\eta=1/10$.
--
--   Differences from the source:
--   - encoding: an algorithm in the adjacency-list model with O(1)-time queries → a Program of the unit-cost RAM (RAM module): constants, +, truncated −, indirect access, jumps, degree / neighbour / edge queries and uniform random choice, one unit per executed instruction; reason: fixes the paper’s operation count; with no multiplication or division the machine is no stronger than the paper’s
--   - encoding: the graph G and its adjacency list → an SGraph whose vertex names are < n, presented by adjacency lists adj in arbitrary order (Presents); reason: the lists are given to the algorithm; their order is not under its control
--   - reading: “with high probability” → for every c > 0 there are constants and a program with failure probability at most n^(−c), for every n ≥ 2; reason: the standard meaning, made explicit by the amplification remark of p. 18 (log n → log(n/ξ))
--   - reading: “with high probability, in O(log² n/(α²ε²)) time answers” → the time bound and the correct answer hold together on the high-probability event; reason: both are under “with high probability” in the printed sentence
--   - reading: O(log² n/(α²ε²)) “for any constant α” → one constant C for all α and ε (depending only on c); reason: α and ε appear explicitly in the bound
--   - encoding: the answer “yes” / “no” → cell 0 holds 1 / 0 when the program halts; reason: output convention
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Lemma 3.1, p. 15

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_RAM

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Lemma 3.1 (p. 15). -/
theorem lemma_3_1 :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ α ε : ℝ, 0 < α → 0 < ε → α * ε ≤ 1 / 100 →
        ∃ P : Program,
          ∀ n : ℕ, 2 ≤ n → ∀ H : SGraph, (∀ v ∈ H.V, v < n) →
            ∀ adj : ℕ → List ℕ, Presents H adj → ∀ v ∈ H.V,
              1 - (n : ℝ) ^ (-c) ≤
                ((runCall P H adj (inputMem n v [] (fun _ => 0) (fun _ => 0))
                    ⌊C * lg n ^ 2 / (α ^ 2 * ε ^ 2)⌋₊).toOuterMeasure
                  {o | ∃ (m : ℕ → ℕ) (st : ℕ), o = some (m, st) ∧
                    (H.Sparse (α * ε) v → m 0 = 1) ∧
                    (¬ H.Sparse ((1 - 1 / 10) * (α * ε)) v → m 0 = 0)}).toReal := by sorry

end FullyDynamicCorrelation.VertexUpdates
