-- Prove2me | Theorems.Thm_FullForesight_Randomized_lemma_4
-- name    : FullForesight.Randomized.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:16:53.595943+00:00
-- url     : https://prove2.me/theorems/1002c54d-4bfa-4584-bf23-1e2dfba31ab7
-- title:
--   Lemma 4 — the adaptivity gap of nonincreasing consecutive intervals with the equalizing distribution is at least $\xi^\star$, with equality on a three-interval instance
-- statement:
--   (i) For every interval-selection instance $(\ell, r, p)$ whose intervals are nonincreasing consecutive and whose distribution $p$ is equalizing,
--   $$\Gamma(\ell, r, p) \ge \xi^\star .$$
--   (ii) $u_1$ lies in $(0, 1)$, $\Phi(u_1) = 0$ with $\Phi(x) = x^4 + x^3 - 2x^2 - 3x + 2$, and $u_1$ is the only root of $\Phi$ in $(0,1)$. Let $u_2 = u_1^2(1 + u_1)$ and consider the three intervals
--   $$[\ell_0, r_0] = [0, 1],\quad [\ell_1, r_1] = [1, 1 + u_1],\quad [\ell_2, r_2] = [1 + u_1, 1 + u_1 + u_2].$$
--   They admit an equalizing probability distribution, and for every equalizing probability distribution $p$ on them, $\Gamma(\ell, r, p) = \xi^\star$.
--
--   Part (i) is the last step of the algorithmic half of Main Result 1; part (ii) shows the bound is attained, by the interval picture of the hard coverage instance of Theorem 1.
--
--   Differences from the source:
--   - reading: "Equality holds for the three-interval instance … with the equalizing distribution" → an equalizing distribution exists and every equalizing distribution gives $\Gamma = \xi^\star$; reason: the paper speaks of the equalizing distribution (unique, App. A.5); stating existence prevents a vacuous equality clause.
--   - encoding: "where $u_1$ is the unique root in $(0,1)$ of $\Phi$" → $u_1$ is a concrete definition (supremum of the roots in $[0,1]$) and the conclusion asserts that it is a root in $(0,1)$ and the only one there; reason: a defined constant needs its defining property in the conclusion.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 9, Lemma 4 (restated and proved pp. 27–29)

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_FullForesight_Randomized_IntervalSelection

namespace FullForesight.Randomized

theorem lemma_4 :
    (∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p →
        IsNonincConsecutive ℓ r → IsEqualizing ℓ r p → xiStar ≤ gap ℓ r p) ∧
      (0 < u1 ∧ u1 < 1 ∧ Phi u1 = 0 ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1, Phi x = 0 → x = u1) ∧
      (∃ p : Fin (2 + 1) → ℝ,
        IsIntervalInstance ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p ∧
          IsEqualizing ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p) ∧
      (∀ p : Fin (2 + 1) → ℝ,
        IsIntervalInstance ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p →
          IsEqualizing ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p →
            gap ![0, 1, 1 + u1] ![1, 1 + u1, 1 + u1 + u2] p = xiStar) := by sorry

end FullForesight.Randomized
