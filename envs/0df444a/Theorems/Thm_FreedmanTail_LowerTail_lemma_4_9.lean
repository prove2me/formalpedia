-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_lemma_4_9
-- name    : FreedmanTail.LowerTail.lemma_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:32:37.096868+00:00
-- url     : https://prove2.me/theorems/29365e02-acff-462f-a95a-8a62ed00d0cd
-- title:
--   (4.9) Lemma — if α > 0 and x > 2 log α, then e^x > αx
-- statement:
--   Let $\alpha>0$ and let $x$ be a real number with $x>2\log\alpha$. Then
--
--   $$
--   e^{x}>\alpha x .
--   $$
--
--   This elementary inequality is the tool that turns the lower bound (4.12c) on $k=a^2/b$ into the estimate (4.17), $\exp(-\delta^2k/8)<1/(8k)$, which controls the error terms of Proposition (4.10).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 109 (PDF p. 10), (4.9) Lemma

import Mathlib

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.9) Lemma, p. 109: if `α > 0` and `x > 2 log α`, then `e^x > αx`. -/
theorem lemma_4_9 (α x : ℝ) (hα : 0 < α) (hx : 2 * Real.log α < x) :
    α * x < Real.exp x := by sorry

end FreedmanTail.LowerTail
