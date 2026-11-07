-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_5_17
-- name    : MatMulTimeLP.lemma_5_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:36.926626+00:00
-- url     : https://prove2.me/theorems/cf4bf2a8-2dbb-45eb-ae72-b288cd95acf7
-- title:
--   Lemma 5.17 — row-query work $O(L\log n)=O(n^2\log^2 n)$
-- statement:
--   Along the execution of Algorithm 3, all row queries, row-query value updates and label repairs, including those during cleanup, take total expected time
--
--   $$O(L\log n)=O(n^2\log^2 n).$$
--
--   That is, there are constants $C,C'$ such that for all $n\ge 2$ and all $H,h,a$ with $\|H\|_2\le 1$, $\|h\|_2\le n$, $a=Hf(a)+h$ and $\|a\|_1\le n$, the expected total operation count over $L=\lceil 8\Lambda\log(64n^{11}(2+320n)^2)\rceil$ iterations is at most $CL\log n$, and $L\log n\le C'n^2\log^2 n$.
--
--   Since a dense row query costs $n$ operations, this is the step where the magnitude labels pay off: large coordinates, whose rows are cheap to query, are selected more often.
--
--   Differences from the source:
--   - encoding: "time" of the row-query operations → the operation bounds of Theorem 5.13 at the labels of each moment (`rowExp`), in coordinate order within a bucket; reason: the machine appears only in `theorem_2_2`, `theorem_4_1` and `theorem_1_1`; the bounds of Theorem 5.13 are its time
--   - reading: $O(L\log n)=O(n^2\log^2 n)$ → `∃ C C', ∀ n ≥ 2`; reason: at $n=1$, $\log 1=0$, so $n=1$ is out of the scope of the asymptotic
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma 5.17, p.37; Theorem 5.13, p.32; Algorithm 5, p.35

import Mathlib
import Definitions.Def_MatMulTimeLP_Chain

open scoped Matrix.Norms.L2Operator

namespace MatMulTimeLP

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma 5.17, p.37: along Algorithm 3, all row queries, row-query
value updates and label repairs, including those during cleanup, take total expected time
`O(L log n) = O(n² log² n)`.

**Formalization Note** "Time" here is the operation count of Theorem 5.13 (p.32), at the labels of the moment
(`rowExp`), since the machine appears only in the mission's statements `theorem_2_2` and `theorem_4_1`. `O(·)` is
`∃ C, ∀ n ≥ 2`, as `log 1 = 0`. Hypotheses: the standing assumptions of Section 5.3, p.25. -/
theorem lemma_5_17 :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ (n : ℕ), 2 ≤ n → ((stepsL n : ℝ) * Real.log n ≤ C' * (n : ℝ) ^ 2 * Real.log n ^ 2) ∧
        ∀ (H : Matrix (Fin n) (Fin n) ℝ) (h a : Fin n → ℝ), ‖H‖ ≤ 1 → l2Norm h ≤ n →
          IsFixPoint H h a → l1Norm a ≤ n →
          rowExp H h (stepsL n) 0 ≤ C * (stepsL n : ℝ) * Real.log n := by sorry

end MatMulTimeLP
