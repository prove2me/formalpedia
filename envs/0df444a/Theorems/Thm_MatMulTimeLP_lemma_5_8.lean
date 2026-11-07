-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_5_8
-- name    : MatMulTimeLP.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:24.119202+00:00
-- url     : https://prove2.me/theorems/58c6bd03-0129-4f03-b629-16eafc7adc36
-- title:
--   Lemma 5.8 — norm bounds after cleanup, $\Lambda=2^{24}n^2$ suffices, $344n$ before cleanup
-- statement:
--   Let $n\ge 1$, $\|H\|_2\le 1$, $\|h\|_2\le n$, and let $z$ be an iterate of Algorithm 3 after cleanup, for any sequence of selected coordinates, with residual $r$. Then:
--
--   1. $|z_i|\le 320n$ for every $i$, and $|\{i:|z_i|\ge s\}|\le 640n/s$ for every $s\ge 1$;
--   2. $\|z\|_1\le 320n\log_2(320n)$, $\|z\|_2\le 512n$ and $\|r\|_2\le 1025n$;
--   3. $\Lambda=2^{24}n^2$ satisfies $\sum_i(2+|z_i|)^2+\|r\|_2^2\le\Lambda$ and $\Lambda-\sum_i(2+|z_i|)^2\ge 4\|r\|_2^2$;
--   4. right after a coordinate step, before cleanup, every coordinate has absolute value less than $344n$.
--
--   This makes the sampling probabilities $w_i/\Lambda$ sum to at most $1$, and supplies the room $U=\Lambda-S\ge 4\|r\|_2^2$ the residual sampler requires.
--
--   Differences from the source:
--   - generalization: the standing assumption $\|a\|_1\le n$ (p.25) → no solution $a$ is mentioned; reason: the proof does not use one, and p.38 applies the lemma "for any sequence of selected coordinates"; the page's case is an instance
--   - encoding: "at every iteration, after cleanup" → every point of `Reachable H h`, the closure of $0$ under "coordinate step, then cleanup"; reason: these are the iterates; a $\bot$ iteration leaves $z$ unchanged
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma 5.8, p.28

import Mathlib
import Definitions.Def_MatMulTimeLP_Chain

open scoped Matrix.Norms.L2Operator

namespace MatMulTimeLP

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma 5.8, p.28, for every iterate of Algorithm 3 and any
sequence of selected coordinates: `|zᵢ| ≤ 320n`; `|{i : |zᵢ| ≥ s}| ≤ 640n/s` for `s ≥ 1`; `‖z‖₁ ≤ 320n log₂(320n)`,
`‖z‖₂ ≤ 512n`, `‖r‖₂ ≤ 1025n`; `Λ = 2²⁴n²` satisfies `∑ᵢ(2 + |zᵢ|)² + ‖r‖₂² ≤ Λ` and
`Λ - ∑ᵢ(2 + |zᵢ|)² ≥ 4‖r‖₂²`; and right after a coordinate step, before cleanup, every coordinate has absolute
value less than `344n`.

**Formalization Note** No solution `a` is needed: the proof uses only `‖H‖₂ ≤ 1` and `‖h‖₂ ≤ n`. -/
theorem lemma_5_8 {n : ℕ} (hn : 1 ≤ n) (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (hH : ‖H‖ ≤ 1) (hh : l2Norm h ≤ n) (z : Fin n → ℝ) (hz : Reachable H h z) :
    (∀ i, |z i| ≤ 320 * n) ∧
    (∀ s : ℝ, 1 ≤ s → ((Finset.univ.filter fun i => s ≤ |z i|).card : ℝ) ≤ 640 * n / s) ∧
    l1Norm z ≤ 320 * n * Real.logb 2 (320 * n) ∧
    l2Norm z ≤ 512 * n ∧
    l2Norm (residual H h z) ≤ 1025 * n ∧
    ∑ i, (2 + |z i|) ^ 2 + ∑ i, residual H h z i ^ 2 ≤ bigLam n ∧
    4 * ∑ i, residual H h z i ^ 2 ≤ bigLam n - ∑ i, (2 + |z i|) ^ 2 ∧
    ∀ i j, |coordStep H h z i j| < 344 * n := by sorry

end MatMulTimeLP
