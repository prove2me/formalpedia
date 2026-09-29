-- Prove2me | Theorems.Thm_OnlineConvexOpt_Introduction_randomized_weighted_majority_mistake_bound
-- name    : OnlineConvexOpt.Introduction.randomized_weighted_majority_mistake_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:07:30.508211+00:00
-- url     : https://prove2.me/theorems/ab683447-05f3-46b0-810b-bf0ebd7885a7
-- title:
--   Lemma 1.4 — Randomized Weighted Majority mistake bound
-- statement:
--   **Lemma 1.4** (Randomized Weighted Majority mistake bound, Hazan, p. 11). Let $M_T$
--   denote the number of mistakes made by RWM until iteration $T$. Then, for any expert
--   $i \in [N]$ and any run of Randomized Weighted Majority with parameter
--   $\varepsilon \in (0, 1/2)$,
--
--   $$
--   \mathbb E[M_T] \;\le\; (1+\varepsilon)\, M_T(i) \;+\; \frac{\log N}{\varepsilon}.
--   $$
--
--   Randomizing the prediction rule (Weighted Majority's deterministic majority vote becomes
--   RWM's sampling proportional to weight) halves both the multiplicative constant, from
--   $2(1+\varepsilon)$ to $(1+\varepsilon)$, and the additive term, from $2\log N/\varepsilon$
--   to $\log N/\varepsilon$, relative to Lemma 1.3.
--
--   **Formalization Note.** `ε ∈ (0, 1/2)` is again the range under which the book's proof is
--   valid; $\mathbb E[M_T]$ is `expectedMistakes`, the deterministic inner product of RWM's
--   probability vector with the $\{0,1\}$-mistake indicator (§1.3.3), not a measure-theoretic
--   expectation over an explicit probability space.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 11, Lemma 1.4

import Mathlib import Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts import Definitions.Def_OnlineConvexOpt_Introduction_RandomizedWeightedMajority

namespace OnlineConvexOpt.Introduction

/-- **Lemma 1.4** (Randomized Weighted Majority mistake bound), Hazan, *Introduction to
Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 11.

"Let `M_T` denote the number of mistakes made by RWM until iteration `T`. Then, for any
expert `i ∈ [N]` we have `E[M_T] ≤ (1 + ε) M_T(i) + log N / ε`."

As in Lemma 1.3, `0 < ε < 1/2` is the range under which the book's own proof (the same
logarithm bound, `-x - x² ≤ log(1 - x) ≤ -x` for `0 < x < 1/2`) is valid, matching Theorem
1.2's explicit range for the corollary that packages this lemma. -/
theorem randomized_weighted_majority_mistake_bound {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (W p : ℕ → Fin N → ℝ)
    (hrun : IsRandomizedWeightedMajorityRun ε expertPredict outcome W p)
    (T : ℕ) (i : Fin N) :
    expectedMistakes expertPredict outcome p T ≤
      (1 + ε) * (expertMistakes expertPredict outcome i T : ℝ) + Real.log N / ε := by sorry

end OnlineConvexOpt.Introduction
