-- Prove2me | Theorems.Thm_IterRoundKMedian_Main_lemma_7_5
-- name    : IterRoundKMedian.Main.lemma_7_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:27:09.925476+00:00
-- url     : https://prove2.me/theorems/a6c91d20-0d0d-41e0-8a6f-a8d0ebe03623
-- title:
--   Lemma 7.5 — the assurance radius is at most V_j + √(10e·V_jM_j) + (5e/2)·M_j
-- statement:
--   Let a client's distance profile be given by weights $y_i\ge0$ with $\sum_iy_i=1$ and distances $d_i\ge0$, and let $V_j$, $M_j$ and the assurance radius $A_j$ be as in `ClientProfile`. Then
--   $$A_j\ \le\ V_j+\sqrt{10e\cdot V_jM_j}+\frac{5e}{2}\,M_j.$$
--
--   The bound depends on the client's profile through its mean absolute deviation: for clients whose distances are nearly equal, $A_j$ is close to $V_j$. Theorem 7.1 combines it with Lemma 7.11.
--
--   Differences from the source:
--
--   - generalization: a client j ∈ C of a complete fractional solution (P_j over F_j with y_i > 0, y(F_j) = 1, d(i, j) from a metric) → any finite family of weights y_i ≥ 0 with Σ y_i = 1 and distances d_i ≥ 0; reason: A_j, V_j and M_j depend only on P_j, which is such a family; zero weights contribute to no quantity
--   - encoding: A_j = the minimum of R + 5e·T_j(R) over admissible R → sInf of the objective over the admissible radii; reason: the minimum exists (p. 65), so it is the infimum; the set is nonempty and bounded below by 0 under the hypotheses
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 66, Lemma 7.5

import Mathlib
import Definitions.Def_IterRoundKMedian_Main_ClientProfile

namespace IterRoundKMedian.Main

open ClientProfile in
theorem lemma_7_5 {ι : Type*} [Fintype ι] (y d : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hy1 : ∑ i, y i = 1) (hd : ∀ i, 0 ≤ d i) :
    A y d ≤ V y d + Real.sqrt (10 * Real.exp 1 * V y d * M y d)
      + 5 * Real.exp 1 / 2 * M y d := by sorry

end IterRoundKMedian.Main
