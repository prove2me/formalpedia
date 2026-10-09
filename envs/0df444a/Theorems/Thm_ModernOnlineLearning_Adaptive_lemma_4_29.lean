-- Prove2me | Theorems.Thm_ModernOnlineLearning_Adaptive_lemma_4_29
-- name    : ModernOnlineLearning.Adaptive.lemma_4_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:26.058216+00:00
-- url     : https://prove2.me/theorems/8e7a6c6a-3b32-439a-97bb-83f94c70bd93
-- title:
--   Lemma 4.29, p. 45 — resolving a square-root implicit inequality
-- statement:
--   Let $a,b,c,x\ge0$ and suppose $x-\sqrt{ax+b}\le c$. Then
--
--   $$x\le\frac a2+c+\sqrt{\frac{a^2}{4}+b+ac}\le a+c+\sqrt{b+ac}.$$
--
--   The lemma converts the implicit regret estimate into an explicit bound in the comparator's cumulative loss.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 4.29, p. 45

import Mathlib

namespace ModernOnlineLearning.Adaptive

/-- Orabona, Lemma 4.29, p. 45. -/
theorem lemma_4_29 (a b c x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hx : 0 ≤ x)
    (himplicit : x - Real.sqrt (a * x + b) ≤ c) :
    x ≤ a / 2 + c + Real.sqrt (a ^ 2 / 4 + b + a * c) ∧
      a / 2 + c + Real.sqrt (a ^ 2 / 4 + b + a * c) ≤
        a + c + Real.sqrt (b + a * c) := by sorry

end ModernOnlineLearning.Adaptive
