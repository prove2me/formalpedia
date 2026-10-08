-- Prove2me | Theorems.Thm_GivenDegreeSeq_GraphLimit_claim_6_3
-- name    : GivenDegreeSeq.GraphLimit.claim_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:27.613976+00:00
-- url     : https://prove2.me/theorems/900a9def-77e9-441e-b638-508001a1b262
-- title:
--   Claim 6.3 — near-expected integer margins admit a 0–1 contingency table
-- statement:
--   Let $0<\delta<\tfrac12$ and let $(p_{ij})$ be an $m\times n$ real matrix with $\delta\le p_{ij}\le1-\delta$ for all $i,j$. Let $(r_i)_{i=1}^m$ and $(c_j)_{j=1}^n$ be integer sequences such that
--
--   1. $\sum_{i=1}^m r_i=\sum_{j=1}^n c_j$;
--   2. $\big|r_i-\sum_{j=1}^n p_{ij}\big|\le\tfrac14\delta^2 n$ for $1\le i\le m$;
--   3. $\big|c_j-\sum_{i=1}^m p_{ij}\big|\le\tfrac14\delta^2 m$ for $1\le j\le n$.
--
--   Then there is a **0–1 contingency table** with row sums $(r_i)$ and column sums $(c_j)$: an $m\times n$ matrix with entries in $\{0,1\}$ whose $i$-th row sums to $r_i$ and whose $j$-th column sums to $c_j$.
--
--   In the proof of Lemma 6.2 this guarantees that the edges between two parts of the vertex set can always be completed to realize a prescribed degree sequence.
--
--   **Formalization Note** The table is a matrix with natural-number entries at most $1$; its row and column sums are compared with the integer margins after casting to $\mathbb Z$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 27, Claim 6.3 (0–1 contingency table defined on p. 26)

import Mathlib

namespace GivenDegreeSeq.GraphLimit

/-- **Claim 6.3** (Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, p. 27). Let `0 < δ < 1/2` and let
`(p_ij)` be an `m × n` matrix with `δ ≤ p_ij ≤ 1 − δ`. Suppose the integer sequences `(r_i)`,
`(c_j)` satisfy `Σ_i r_i = Σ_j c_j`, `|r_i − Σ_j p_ij| ≤ δ²n/4` for every row `i` and
`|c_j − Σ_i p_ij| ≤ δ²m/4` for every column `j`. Then there is a 0–1 contingency table with row
sums `(r_i)` and column sums `(c_j)`: an `m × n` matrix with entries in `{0, 1}` whose `i`-th row
sums to `r_i` and whose `j`-th column sums to `c_j`. -/
theorem claim_6_3 (m n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i j, δ ≤ p i j ∧ p i j ≤ 1 - δ)
    (r : Fin m → ℤ) (c : Fin n → ℤ) (hsum : ∑ i, r i = ∑ j, c j)
    (hr : ∀ i, |(r i : ℝ) - ∑ j, p i j| ≤ 1 / 4 * δ ^ 2 * n)
    (hc : ∀ j, |(c j : ℝ) - ∑ i, p i j| ≤ 1 / 4 * δ ^ 2 * m) :
    ∃ M : Matrix (Fin m) (Fin n) ℕ, (∀ i j, M i j ≤ 1) ∧
      (∀ i, ((∑ j, M i j : ℕ) : ℤ) = r i) ∧ (∀ j, ((∑ i, M i j : ℕ) : ℤ) = c j) := by sorry

end GivenDegreeSeq.GraphLimit
