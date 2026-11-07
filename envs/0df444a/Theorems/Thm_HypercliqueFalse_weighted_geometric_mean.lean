-- Prove2me | Theorems.Thm_HypercliqueFalse_weighted_geometric_mean
-- name    : HypercliqueFalse.weighted_geometric_mean
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:29:59.845096+00:00
-- url     : https://prove2.me/theorems/a79da1d2-bb74-47c5-8baa-0af146841526
-- title:
--   Proof of Lemma 4.3 — the weighted geometric mean bound
-- statement:
--   Let $a, b, c \ge 1$ be reals and $0 < \epsilon \le 2$. Then
--   $$
--   \min\{ab\,c^{1-\epsilon},\ a^{1-\epsilon}b\,c^2,\ a\,b^{1-\epsilon}c^2\} \le (ab)^{1-\epsilon^2/8}\,c^{1-3\epsilon/4+\epsilon^2/4} \le (abc)^{1-\epsilon^2/8}.
--   $$
--   (The first inequality bounds the minimum by the weighted geometric mean with weights $1-\epsilon/4$, $\epsilon/8$, $\epsilon/8$.)
--
--   In the proof of Lemma 4.3 this turns the running time of the fastest of three algorithms into $O(N^4n^{h-3}(abc)^{1-\delta})$ with $\delta = \epsilon^2/8$.
--
--   Differences from the source:
--   - generalization: a, b, c positive integers (matrix dimensions), 0 < ϵ_{h−1} ≤ ϵ₂ → real a, b, c ≥ 1 and 0 < ε ≤ 2; reason: the chain holds there (the weights are nonnegative for ε ≤ 4, the last step needs ε ≤ 2 and c ≥ 1); specializes to the paper's values
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Lemma 4.3, p.12

import Mathlib

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The weighted-geometric-mean bound of the base case.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of
Lemma 4.3, p.12: "Bounding the minimum by a weighted geometric mean with weights 1−ϵ_{h−1}/4,
ϵ_{h−1}/8, and ϵ_{h−1}/8, we obtain min{abc^{1−ϵ_{h−1}}, a^{1−ϵ_{h−1}}bc², ab^{1−ϵ_{h−1}}c²} ≤
(ab)^{1−ϵ²_{h−1}/8} c^{1−3ϵ_{h−1}/4+ϵ²_{h−1}/4} ≤ (abc)^{1−ϵ²_{h−1}/8}".

Both inequalities of the chain, for real `a, b, c ≥ 1` and `0 < ε ≤ 2`. -/
theorem weighted_geometric_mean (a b c ε : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hε : 0 < ε) (hε2 : ε ≤ 2) :
    min (min (a * b * c ^ (1 - ε)) (a ^ (1 - ε) * b * c ^ 2)) (a * b ^ (1 - ε) * c ^ 2) ≤
        (a * b) ^ (1 - ε ^ 2 / 8) * c ^ (1 - 3 * ε / 4 + ε ^ 2 / 4) ∧
      (a * b) ^ (1 - ε ^ 2 / 8) * c ^ (1 - 3 * ε / 4 + ε ^ 2 / 4) ≤
        (a * b * c) ^ (1 - ε ^ 2 / 8) := by sorry

end HypercliqueFalse
