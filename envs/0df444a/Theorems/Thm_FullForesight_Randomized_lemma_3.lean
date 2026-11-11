-- Prove2me | Theorems.Thm_FullForesight_Randomized_lemma_3
-- name    : FullForesight.Randomized.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:16:53.630245+00:00
-- url     : https://prove2.me/theorems/4035e8b0-e140-4ca4-ad23-7e40b7106b7b
-- title:
--   Lemma 3 — nonincreasing consecutive intervals with the equalizing distribution are the worst case of interval selection
-- statement:
--   Let $\alpha \in [0, 1]$. Suppose that $\Gamma(\ell, r, p) \ge \alpha$ for every interval-selection instance $(\ell, r, p)$ (any $N \ge 0$) whose intervals are nonincreasing consecutive and whose distribution is equalizing. Then
--   $$\Gamma(\ell, r, p) \ge \alpha$$
--   for every interval-selection instance $(\ell, r, p)$.
--
--   This is the lossless reduction of §2.5: a lower bound on the adaptivity gap needs to be proved only for the structured family, which Lemma 4 does.
--
--   Differences from the source: none.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 9, Lemma 3 (restated and proved pp. 25–26)

import Mathlib
import Definitions.Def_FullForesight_Randomized_IntervalSelection

namespace FullForesight.Randomized

theorem lemma_3 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p →
      IsNonincConsecutive ℓ r → IsEqualizing ℓ r p → α ≤ gap ℓ r p) :
    ∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p → α ≤ gap ℓ r p := by sorry

end FullForesight.Randomized
