-- Prove2me | Theorems.Thm_IntervalToDynamic_lemma_11
-- name    : IntervalToDynamic.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:24:12.912728+00:00
-- url     : https://prove2.me/theorems/0b22ae1f-7cfe-42e9-af5b-b2662f4e1a0e
-- title:
--   Lemma 11 — the greedy partition: $P_{I_j}\le B/|I_j|^\varepsilon$ and the bound on $K$
-- statement:
--   Let $T,d$ be positive integers, $B>0$, $\varepsilon\ge0$ and $u_1,\dots,u_T\in\mathbb R^d$, and write $P_I=\sum_{t=a+1}^b\|u_t-u_{t-1}\|_2$ for $I=[a,b]$. Partition $[T]$ from left to right, greedily extending each interval $I$ as long as possible subject to $P_I\le B/|I|^\varepsilon$. If $P_T>0$, the resulting intervals $I_1,\dots,I_K$ satisfy, for every $j\in[K]$,
--   $$
--   P_{I_j}\le\frac{B}{|I_j|^\varepsilon},\qquad K\le\Bigl\lceil\Bigl(\frac{P_T}{B}\Bigr)^{\frac1{1+\varepsilon}}(2T)^{\frac\varepsilon{1+\varepsilon}}\Bigr\rceil .
--   $$
--
--   The partition converts a global path length into few intervals of small local path length.
--
--   Differences from the source:
--   - encoding: "Partition [T]" in words → an explicit clause `IsIntervalPartition T 1 (greedyPartition B ε u T)`; reason: the page asserts that the intervals partition [T], and later steps use it
--   - encoding: intervals I_1, …, I_K → a list of pairs (a, b), with K its length and |I| = b − a + 1; reason: same objects
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 11, p.29

import Mathlib
import Definitions.Def_IntervalToDynamic_greedyPartition
import Definitions.Def_IntervalToDynamic_IsIntervalPartition
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs
open ModernOnlineLearning.Dynamic (dynamicRegret pathLength)

namespace IntervalToDynamic

/-- Lemma 11 (partition for first differences). Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Lemma 11, p.29.

Let `T, d` be positive integers, `B > 0`, `ε ≥ 0`, and `u_1, …, u_T ∈ ℝ^d`. Partition `[T]` from left
to right, greedily extending each interval `I` as long as possible subject to `P_I ≤ B/|I|^ε`. If
`P_T > 0`, the resulting intervals `I_1, …, I_K` satisfy, for every `j ∈ [K]`,
`P_{I_j} ≤ B/|I_j|^ε`, and `K ≤ ⌈(P_T/B)^{1/(1+ε)} (2T)^{ε/(1+ε)}⌉`.

**Formalization Note.** The first clause records that the greedy list is a partition of `[T]`, which
the page says in words. At `P_T = 0` the printed ceiling is `0` while `K = 1`, so `P_T > 0` stays. -/
theorem lemma_11 {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T) (B ε : ℝ) (hB : 0 < B) (hε : 0 ≤ ε)
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (hP : 0 < pathLength u T) :
    IsIntervalPartition T 1 (greedyPartition B ε u T) ∧
    (∀ p ∈ greedyPartition B ε u T,
      pathLengthOn u p.1 p.2 ≤ B / ((p.2 - p.1 + 1 : ℕ) : ℝ) ^ ε) ∧
    (greedyPartition B ε u T).length ≤
      ⌈(pathLength u T / B) ^ (1 / (1 + ε)) * (2 * (T : ℝ)) ^ (ε / (1 + ε))⌉₊ := by sorry

end IntervalToDynamic
