-- Prove2me | Theorems.Thm_GivenDegreeSeq_Interior_erdos_gallai
-- name    : GivenDegreeSeq.Interior.erdos_gallai
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:28.521984+00:00
-- url     : https://prove2.me/theorems/48561f39-0a7f-4164-ad6f-bfbcf36eee92
-- title:
--   Erdős–Gallai criterion for degree sequences of simple graphs
-- statement:
--   Let $d_1\ge d_2\ge\cdots\ge d_n$ be nonnegative integers. Then $d_1,\dots,d_n$ is the degree sequence of a simple graph on $n$ vertices if and only if $\sum_{i=1}^n d_i$ is even and, for each $1\le k\le n$,
--   $$\sum_{i=1}^k d_i\le k(k-1)+\sum_{i=k+1}^n\min\{d_i,k\}.$$
--
--   This classical theorem (Erdős–Gallai, 1960) is cited, not proved, in the paper; it is the finite statement of which condition (ii) of Proposition 1.2 is the continuum version, and the proof of Proposition 1.2 uses it in both directions.
--
--   **Formalization Note** The sequence is `d : Fin n → ℕ`, nonincreasing; the paper's index range $1\le i\le k$ is `i.val < k` and $k+1\le i\le n$ is `k ≤ i.val`. $k-1$ is natural-number subtraction with $k\ge1$, so it is exact.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 5, Remark 1 (restated p. 23); cited from P. Erdős and T. Gallai, Mat. Lapok 11 (1960) 264–274

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_IsGraphic

namespace GivenDegreeSeq.Interior

/-- **Erdős–Gallai criterion** (Remark 1, p. 5; restated p. 23; cited from Erdős–Gallai 1960).
Let `d_1 ≥ d_2 ≥ ⋯ ≥ d_n` be nonnegative integers (here `d : Fin n → ℕ`, nonincreasing, with
the paper's `d_i` equal to `d ⟨i − 1, _⟩`). Then `d` is the degree sequence of a simple graph on
`n` vertices iff `Σ_{i=1}^n d_i` is even and, for each `1 ≤ k ≤ n`,
`Σ_{i=1}^k d_i ≤ k(k − 1) + Σ_{i=k+1}^n min{d_i, k}`.
In `Fin n` the paper's range `1 ≤ i ≤ k` is `i.val < k` and `k + 1 ≤ i ≤ n` is `k ≤ i.val`;
`k - 1` is natural subtraction with `k ≥ 1`. -/
theorem erdos_gallai (n : ℕ) (d : Fin n → ℕ) (hd : Antitone d) :
    IsGraphic d ↔
      (Even (∑ i, d i) ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ n →
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), d i ≤
            k * (k - 1) + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), min (d i) k) := by sorry

end GivenDegreeSeq.Interior
