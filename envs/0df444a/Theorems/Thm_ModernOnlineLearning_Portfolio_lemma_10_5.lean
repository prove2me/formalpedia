-- Prove2me | Theorems.Thm_ModernOnlineLearning_Portfolio_lemma_10_5
-- name    : ModernOnlineLearning.Portfolio.lemma_10_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:37.828072+00:00
-- url     : https://prove2.me/theorems/d1186dcc-a0e7-42e8-96d4-e7db974855f9
-- title:
--   Lemma 10.5, p. 174 — ratio of sums is bounded by the largest component ratio
-- statement:
--   Let $T\ge1$, and let $a_1,\ldots,a_T$ and $b_1,\ldots,b_T$ be nonnegative real numbers. With $a/0=+\infty$ for $a>0$ and $0/0=0$,
--
--   $$\frac{\sum_{t=1}^{T}a_t}{\sum_{t=1}^{T}b_t}\le\max_{1\le t\le T}\frac{a_t}{b_t}.$$
--
--   The lemma reduces a ratio of sums to the worst component ratio, and is used to compare a market sequence with single-stock sequences.
--
--   **Formalization Note** The quotients are encoded in extended nonnegative reals, whose zero-denominator behavior matches the stated convention. $T\ge1$ makes the maximum nonempty.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 10.5, p. 174

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Setting
set_option autoImplicit false

namespace ModernOnlineLearning.Portfolio

/-- Lemma 10.5, p. 174. `ENNReal` realizes the printed conventions
`a/0=+∞` for `a>0` and `0/0=0`. -/
theorem lemma_10_5 {T : ℕ} (hT : 1 ≤ T) (a b : Fin T → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) :
    ENNReal.ofReal (∑ t, a t) / ENNReal.ofReal (∑ t, b t) ≤
      ⨆ t : Fin T, ENNReal.ofReal (a t) / ENNReal.ofReal (b t) := by sorry

end ModernOnlineLearning.Portfolio
