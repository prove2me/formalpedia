-- Prove2me | Theorems.Thm_ModernOnlineLearning_Classification_lemma_4_29
-- name    : ModernOnlineLearning.Classification.lemma_4_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:30:27.567504+00:00
-- url     : https://prove2.me/theorems/b93250c2-f056-4ece-90c5-a3ad8c81026d
-- title:
--   Lemma 4.29, p. 45 — explicit bound from an implicit square-root inequality
-- statement:
--   Let $a,b,c,x$ be nonnegative real numbers satisfying $x-\sqrt{ax+b}\le c$. Then
--
--   $$
--   x\le\frac a2+c+\sqrt{\frac{a^2}{4}+b+ac}
--   \le a+c+\sqrt{b+ac}.
--   $$
--
--   This algebraic lemma converts an implicit regret or mistake inequality into an explicit bound.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 4.29, p. 45

import Mathlib

namespace ModernOnlineLearning.Classification

/-- Orabona, Lemma 4.29, p. 45. -/
theorem lemma_4_29 (a b c x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hx : 0 ≤ x)
    (h : x - Real.sqrt (a * x + b) ≤ c) :
    x ≤ a / 2 + c + Real.sqrt (a ^ 2 / 4 + b + a * c) ∧
      a / 2 + c + Real.sqrt (a ^ 2 / 4 + b + a * c) ≤
        a + c + Real.sqrt (b + a * c) := by sorry

end ModernOnlineLearning.Classification
