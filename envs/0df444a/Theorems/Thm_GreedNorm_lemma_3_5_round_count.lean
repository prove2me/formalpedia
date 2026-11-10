-- Prove2me | Theorems.Thm_GreedNorm_lemma_3_5_round_count
-- name    : GreedNorm.lemma_3_5_round_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:43:51.462655+00:00
-- url     : https://prove2.me/theorems/55342a48-5159-4dad-b4ae-7728eef0d0d9
-- title:
--   Proof of Lemma 3.5 — after $\frac1\alpha\ln n$ rounds no element remains (corrected: $k\ge1$)
-- statement:
--   Let $0<\alpha\le1$ and let $r_k$ be the number of elements still unassigned after $k$ rounds, with $r_0\le n$ and $r_{k+1}\le(1-\alpha)\,r_k$ for every $k$. Then
--
--   1. $r_k=0$ for every $k$ with $n(1-\alpha)^k<1$;
--   2. in particular $r_k=0$ for every $k\ge1$ with $k\ge\frac1\alpha\ln n$.
--
--   This bounds the number of assignments in the cover built by Lemma 3.5.
--
--   **Formalization Note** $\ln$ is `Real.log` of $n$ as a real ($\ln 0=0$).
--
--   Differences from the source:
--   - correction: after (1/α) ln n applications the number of remaining elements is less than 1 → r_k = 0 for k ≥ 1 with k ≥ (1/α) ln n; reason: counterexample: n = 1 gives (1/α) ln 1 = 0 applications, after which r_0 = 1 element remains (1·exp(0) = 1 is not < 1)
--   - generalization: the bound n·exp(−ln n) = 1 after (1/α) ln n rounds → also r_k = 0 whenever n(1 − α)^k < 1; reason: sharper form of the same argument; it implies the corrected clause for k ≥ 1
--   - encoding: the fraction of elements that remain is (1 − α) → r : ℕ → ℕ with r_0 ≤ n and r_{k+1} ≤ (1 − α) r_k; reason: the number of remaining elements per round, as the proof uses it
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), proof of Lemma 3.5, p.7 (PDF 9)

import Mathlib

namespace GreedNorm

/-- **The round count of the covering step** (the proof of Lemma 3.5, corrected: `k ≥ 1`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), proof of Lemma 3.5, p.7 (PDF 9): "The fraction of elements that remain is (1 − α) <
exp(−α). Thus, by repeatedly applying the α-approximation algorithm on the unassigned elements, we
get that after (1/α) ln n applications, the number of remaining elements is less than
n · exp(−ln n) = 1."

Let `0 < α ≤ 1` and let `r_k` be the number of elements remaining after `k` rounds, with
`r_0 ≤ n` and `r_{k+1} ≤ (1 − α) r_k`. Then
1. `r_k = 0` for every `k` with `n (1 − α)^k < 1`;
2. in particular `r_k = 0` for every `k ≥ 1` with `k ≥ (1/α) ln n`.

**Formalization Note** `ln` is `Real.log` of the cast of `n` (`Real.log 0 = 0`). -/
theorem lemma_3_5_round_count (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (r : ℕ → ℕ)
    (h0 : r 0 ≤ n) (hstep : ∀ j, (r (j + 1) : ℝ) ≤ (1 - α) * (r j : ℝ)) :
    (∀ k : ℕ, (n : ℝ) * (1 - α) ^ k < 1 → r k = 0) ∧
      (∀ k : ℕ, 1 ≤ k → 1 / α * Real.log (n : ℝ) ≤ (k : ℝ) → r k = 0) := by sorry

end GreedNorm
