-- Prove2me | Theorems.Thm_OnlineConvexOpt_Introduction_weighted_majority_mistake_bound
-- name    : OnlineConvexOpt.Introduction.weighted_majority_mistake_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:06:50.984985+00:00
-- url     : https://prove2.me/theorems/4fb60224-0a6d-4725-abaa-ebe96b850123
-- title:
--   Lemma 1.3 — Weighted Majority mistake bound
-- statement:
--   **Lemma 1.3** (Weighted Majority mistake bound, Hazan, p. 9). Denote by $M_T$ the
--   number of mistakes the algorithm makes until time $T$, and by $M_T(i)$ the number of mistakes
--   made by expert $i$ until time $T$. Then, for any expert $i \in [N]$ and any run of the
--   Weighted Majority algorithm with parameter $\varepsilon \in (0, 1/2)$,
--
--   $$
--   M_T \;\le\; 2(1+\varepsilon)\, M_T(i) \;+\; \frac{2\log N}{\varepsilon}.
--   $$
--
--   The bound holds simultaneously for every expert $i$, so it applies in particular to whichever
--   expert made the fewest mistakes. Together with Theorem 1.1 it shows the deterministic factor of
--   $2$ is essentially unavoidable but the additive term can be made arbitrarily small relative to
--   $T$ by choosing $\varepsilon$ appropriately.
--
--   **Formalization Note.** `ε ∈ (0, 1/2)` is the range under which the book's own proof (via
--   $-x - x^2 \le \log(1-x) \le -x$ for $0 < x < 1/2$) is valid, matching the explicit range
--   Theorem 1.2 states for the corollary that packages this lemma.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 9, Lemma 1.3

import Mathlib import Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts import Definitions.Def_OnlineConvexOpt_Introduction_WeightedMajority

namespace OnlineConvexOpt.Introduction

/-- **Lemma 1.3** (Weighted Majority mistake bound), Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 9.

"Denote by `M_T` the number of mistakes the algorithm makes until time `T`, and by `M_T(i)`
the number of mistakes made by expert `i` until time `T`. Then, for any expert `i ∈ [N]` we
have `M_T ≤ 2(1 + ε) M_T(i) + 2 log N / ε`."

`0 < ε < 1/2` is the range under which the book's own proof of this lemma (via the bound
`-x - x² ≤ log(1 - x) ≤ -x` for `0 < x < 1/2`) is valid; the same range is stated explicitly
for Theorem 1.2, the corollary that packages this lemma together with Lemma 1.4. -/
theorem weighted_majority_mistake_bound {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (W : ℕ → Fin N → ℝ)
    (algPredict : ℕ → Bool) (hrun : IsWeightedMajorityRun ε expertPredict outcome W algPredict)
    (T : ℕ) (i : Fin N) :
    (algMistakes algPredict outcome T : ℝ) ≤
      2 * (1 + ε) * (expertMistakes expertPredict outcome i T : ℝ) + 2 * Real.log N / ε := by sorry

end OnlineConvexOpt.Introduction
