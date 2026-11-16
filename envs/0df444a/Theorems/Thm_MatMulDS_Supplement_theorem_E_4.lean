-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_E_4
-- name    : MatMulDS.Supplement.theorem_E_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:24:27.77638+00:00
-- url     : https://prove2.me/theorems/a96b11e7-0de4-4f3a-bed1-519f53d00160
-- title:
--   Theorem E.4 — exponential-shift clustering: a strong $(2\lceil6R\ln n\rceil,1+56/R)$-LDSND in $O((m+nR)\log^2n)$ w.h.p.
-- statement:
--   Let $G$ be an undirected unweighted graph with $n\ge2$ vertices and $m$ edges, and let $2\le R\le n$. There is a randomized algorithm that always returns a strong $(2\lceil6R\ln n\rceil,\,1+56/R)$-LDSND $\mathcal C$ of $G$ (Definition E.3) and that runs in
--   $$O((m+nR)\log^2n)$$
--   time with high probability.
--
--   With $R=2$ this answers questions of Saha, Xu and Ye on decompositions with polylogarithmic diameter and overlap in near-linear time; it is the decomposition step of Theorem E.5.
--
--   Differences from the source:
--   - encoding: a randomized algorithm on the word RAM → a program of the mission's machine over $\mathbb F_2$, whose coin instruction draws a uniform bit, every step counted, every word size $w\ge K\lceil\log_2(n+1)\rceil+K$; reason: a word RAM with random bits; the field cells over $\mathbb F_2$ are a bit array
--   - reading: "always returns" → every halting run, on every coin sequence, is correct, and the run halts with probability one; reason: a Las Vegas guarantee; "returns" implies halting
--   - reading: "with high probability" → for every $c>0$ a constant $C$ (depending on $c$) with probability at least $1-n^{-c}$; reason: the form the paper's own proofs give (Theorems E.4, E.5, Lemma J.2; SUPPLEMENT decision 1)
--   - encoding: a graph $G=(V,E)$ with $n$ vertices and $m$ edges → $V=\{0,\dots,n-1\}$, any adjacency-list representation $L$ of $G$ as input words, $m$ the number of edges; reason: the source's input convention (§3: graphs given by adjacency lists)
--   - reading: $2\le R\le n$ real, an input of the algorithm → $R=a/b$ given exactly by natural-number words $a,b$ with $b\ge1$; word size $w\ge K\lceil\log_2(n+a+b+1)\rceil+K$; reason: an algorithm input must be representable; the guarantees depend on $R$ exactly, so it cannot be rounded
--   - encoding: output $\mathcal C$ → word cell $v$ holds the label of the cell of $v$; the cells are the label classes; reason: a layout of a partition
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem E.4, p.98 (PDF p.100); Definition E.3, p.97

import Mathlib
import Definitions.Def_MatMulDS_Supplement_adjWords
import Definitions.Def_MatMulDS_Supplement_coinFrac

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS.Supplement

/-- **Theorem E.4, p.98** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `G` be an
undirected unweighted graph with `n ≥ 2` vertices and `m` edges, and let `2 ≤ R ≤ n`. There is a randomized algorithm that always
returns a strong `(2⌈6R ln n⌉, 1 + 56/R)`-LDSND `C` of `G` and that runs in `O((m + nR) log² n)` time with high probability.

**Formalization Note.**
* Randomized word RAM over `𝔽₂` (`coinFrac`), all steps counted. `R` is an input, so it is given exactly, as a fraction `a/b` of
  natural numbers (words `a, b` after `adjWords L`); the word size is `w ≥ K⌈log₂(n + a + b + 1)⌉ + K`. Output: word cell `v` holds
  the label of the cell of `v`; the cells are the label classes (`IsStrongLDSND`, with the strong diameter `diam(G[C_i])`).
* `ln` is the natural logarithm; "always returns" and "with high probability" as in Theorem 8.11. -/
theorem theorem_E_4 :
    ∃ (P : List AInstr) (K : ℕ),
      (∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L →
        ∀ a b : ℕ, 1 ≤ b → (2 : ℝ) ≤ (a : ℝ) / b → (a : ℝ) / b ≤ n →
        ∀ w : ℕ, K * Nat.clog 2 (n + a + b + 1) + K ≤ w →
          AlwaysReturns P w (adjWords L ++ [(a : ℤ), (b : ℤ)]) fun st =>
            ∃ lab : Fin n → ℕ, (∀ v : Fin n, (st (v : ℕ)).toInt = lab v) ∧
              IsStrongLDSND G lab (2 * ⌈6 * ((a : ℝ) / b) * Real.log n⌉₊) (1 + 56 / ((a : ℝ) / b))) ∧
      ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L →
        ∀ a b : ℕ, 1 ≤ b → (2 : ℝ) ≤ (a : ℝ) / b → (a : ℝ) / b ≤ n →
        ∀ w : ℕ, K * Nat.clog 2 (n + a + b + 1) + K ≤ w →
          1 - (n : ℝ) ^ (-c) ≤
            coinFrac P w (adjWords L ++ [(a : ℤ), (b : ℤ)])
              ⌈C * ((G.edgeSet.ncard : ℝ) + n * ((a : ℝ) / b)) * Real.log n ^ 2⌉₊ fun _ => True := by sorry

end MatMulDS.Supplement
