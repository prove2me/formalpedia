-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_sparse_flip_word_bounds
-- name    : KSATSingleFlip.Connect.sparse_flip_word_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:25:19.685204+00:00
-- url     : https://prove2.me/theorems/3b6cbbe6-1dff-4662-a581-f13d05856c5f
-- title:
--   Sparse input and compact flip-list word bounds
-- statement:
--   If $m\le cn$, then a sparse width-$k$ instance, initial assignment and requested variable occupy at most $4+(2kc+1)n$ abstract words. If a compact flip list has at most $A\ln n$ flips with $A\ge0$, then its initial assignment and flip list occupy at most $(1+A)n+1$ abstract words. These are representation-size bounds; they do not establish the existence or running time of an algorithm.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, compact path representation printed p. 32 (PDF p. 34) and Theorem 1.3 printed p. 4, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SparseFlip

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Sparse input and logarithmic flip output have linear abstract word size. -/
theorem sparse_flip_word_bounds (n k m c : ℕ) (hn : 0 < n) (hm : m ≤ c * n) :
    sparseFlipInputWords n k m ≤ 4 + (2 * k * c + 1) * n ∧
    ∀ (p : FlipListPath n) (A : ℝ), 0 ≤ A →
      (p.flips.length : ℝ) ≤ A * Real.log n →
      (p.wordCount : ℝ) ≤ (1 + A) * n + 1 := by
  sorry

end KSATSingleFlip.Connect
