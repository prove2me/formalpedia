-- Prove2me | Theorems.Thm_IterRoundKMedian_Main_theorem_1_1
-- name    : IterRoundKMedian.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:28:50.406194+00:00
-- url     : https://prove2.me/theorems/6ebfd483-33cb-41a8-b51a-fe4cef43c817
-- title:
--   Theorem 1.1 — a randomized polynomial-time 1.9999-approximation for metric k-median
-- statement:
--   There exist a function $\mathcal A$ on pairs of bit strings and a polynomial $q$ such that $\mathcal A$ is a randomized polynomial-time $1.9999$-approximation algorithm for metric k-median (`IsRandomizedApprox`): $\mathcal A$ is computed in polynomial time by a finite-alphabet multi-stack Turing machine on input (encoded instance, seed); for every metric k-median instance $I$ (rational metric, any clients, any nonempty facility set, any $k\ge1$) and every seed $s$ of length $q(|\mathrm{enc}(I)|)$ it outputs a nonempty set $S_s$ of at most $k$ facilities; and
--   $$\frac{1}{2^{q(|\mathrm{enc}(I)|)}}\sum_{s}\mathrm{cost}(S_s)\ \le\ 1.9999\cdot\mathrm{OPT}(I).$$
--
--   The factor 2 had been the barrier for LP-based k-median algorithms; this theorem shows it can be beaten, and that the integrality gap of the standard relaxation is below 2 when a constant number of extra facilities is allowed.
--
--   Differences from the source:
--
--   - reading: randomized polynomial-time algorithm; expected cost → a function of (encoded instance, uniformly random seed of length q(|enc I|)) computed in worst-case polynomial time by a finite-alphabet TM2 machine (FinitePolyTime); the expectation is the average over seeds; reason: the paper fixes no machine model; this is the stronger worst-case-time, fair-coin reading, which implies the expected-time reading of p. 62
--   - encoding: a metric d on C ∪ F with numeric distances → n points Fin n with a ℚ-valued metric, clients and facilities arbitrary (possibly overlapping) subsets of the points, encoded in binary (encodeRat); reason: a polynomial-time algorithm needs a finite encoding of the input; the cost depends only on distances between C and F, so points outside C ∪ F change no instance
--   - encoding: returns at most k facilities → on every seed the output is the mask of a nonempty S ⊆ F with |S| ≤ k; reason: d(j, ∅) is undefined; with k ≥ 1 adding a facility never raises the cost
--   - encoding: a set F of facilities → F nonempty; reason: with F = ∅ and C ≠ ∅ no solution exists; the condition only excludes undefined instances
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 5, Theorem 1.1 (proved in §8, pp. 70–71)

import Mathlib
import Definitions.Def_IterRoundKMedian_Main_Instance
import Definitions.Def_IterRoundKMedian_Main_RandomizedApprox

namespace IterRoundKMedian.Main

theorem theorem_1_1 :
    ∃ (alg : List Bool × List Bool → List Bool) (q : Polynomial ℕ),
      IsRandomizedApprox (19999 / 10000) alg q := by sorry

end IterRoundKMedian.Main
