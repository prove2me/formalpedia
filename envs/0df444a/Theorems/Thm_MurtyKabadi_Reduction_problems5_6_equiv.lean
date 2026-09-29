-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_problems5_6_equiv
-- name    : MurtyKabadi.Reduction.problems5_6_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:14:06.134527+00:00
-- url     : https://prove2.me/theorems/bcd9f075-7ca9-42cf-a35f-76d9fe85f2f2
-- title:
--   Proof of Theorem 1, p. 124 — Problems 5 and 6 are equivalent
-- statement:
--   Let $d_0; d_1, \dots, d_n$ be positive integers and let $\delta$ be an integer with
--   $$\delta > 4\Big(d_0 \sum_{j=1}^n d_j\Big)^2 n^3.$$
--   With $f_1$ and the polytope $P = \{(y,s) : y, s \ge 0,\ \sum_j (y_j + s_j) = n\}$ as defined for the reduction, the subset sum instance is solvable if and only if there is $(y, s) \in P$ with
--   $$f_1(y, s) \le 0.$$
--
--   This is the first link of the chain from subset sum (Problem 5) to Problem 4: $f_1$ is a sum of nonnegative terms on $P$ that vanishes exactly at the $0$–$1$ solutions $y$ with $s = e - y$.
--
--   **Formalization Note** Only $\delta \ge 0$ is used for this step; the hypotheses are those of the whole reduction.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 124, proof of Theorem 1, first paragraph (Problems 5 and 6 are equivalent)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_SubsetSum
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem problems5_6_equiv {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ) :
    SubsetSumSolvable d d0 ↔ ∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0 := by sorry

end MurtyKabadi.Reduction
