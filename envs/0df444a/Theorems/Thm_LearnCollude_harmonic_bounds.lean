-- Prove2me | Theorems.Thm_LearnCollude_harmonic_bounds
-- name    : LearnCollude.harmonic_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:26.197687+00:00
-- url     : https://prove2.me/theorems/ad7cf01c-a4db-48c2-bd10-d9dd6f12db7c
-- title:
--   (68), (92) (corrected: ≤ at $t=1$) — bounds on generalized harmonic numbers
-- statement:
--   Let $H_t^r=\sum_{i\le t}i^{-r}$. For $0<r<1$ and $t\ge1$,
--   $$
--   H_t^r\le 1+\frac{t^{1-r}-1}{1-r},
--   $$
--   with strict inequality for $t\ge2$. For $\alpha>0$ and $c\ge1$,
--   $$
--   1+\frac{c^{1+\alpha}-1}{1+\alpha}\le H_c^{-\alpha}\le\frac{(c+1)^{1+\alpha}-1}{1+\alpha}.
--   $$
--   These bounds control the sums of the tuning sequences over time in the regret analysis.
--
--   Differences from the source:
--   - correction: (68) H_t^r < 1 + (t^{1−r} − 1)/(1 − r) → ≤ for t ≥ 1, and < for t ≥ 2; reason: at t = 1 both sides equal 1
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), eq. (68), p. 41, and eq. (92), p. 46

import Mathlib
import Definitions.Def_LearnCollude_harmonic

namespace LearnCollude

/-- **Bounds on generalized harmonic numbers**, Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06),
eq. (68), p. 41, and eq. (92), p. 46.

For `0 < r < 1`: `H_t^r ≤ 1 + (t^{1−r} − 1)/(1 − r)` for `t ≥ 1`, strictly for `t ≥ 2`. For `α > 0`
and `c ≥ 1`: `1 + (c^{1+α} − 1)/(1 + α) ≤ H_c^{−α} ≤ ((c + 1)^{1+α} − 1)/(1 + α)`.

**Formalization Note** The printed (68) is strict for all `t`; at `t = 1` both sides equal `1`. -/
theorem harmonic_bounds :
    (∀ r : ℝ, 0 < r → r < 1 → ∀ t : ℕ, 1 ≤ t →
      harmonic t r ≤ 1 + ((t : ℝ) ^ (1 - r) - 1) / (1 - r) ∧
      (2 ≤ t → harmonic t r < 1 + ((t : ℝ) ^ (1 - r) - 1) / (1 - r))) ∧
    (∀ α : ℝ, 0 < α → ∀ c : ℕ, 1 ≤ c →
      1 + ((c : ℝ) ^ (1 + α) - 1) / (1 + α) ≤ harmonic c (-α) ∧
      harmonic c (-α) ≤ (((c : ℝ) + 1) ^ (1 + α) - 1) / (1 + α)) := by sorry

end LearnCollude
