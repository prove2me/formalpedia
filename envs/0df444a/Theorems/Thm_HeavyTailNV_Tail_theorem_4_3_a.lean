-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_theorem_4_3_a
-- name    : HeavyTailNV.Tail.theorem_4_3_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:15.200026+00:00
-- url     : https://prove2.me/theorems/3806cfb3-758b-4cb7-b4a4-e544444b0a30
-- title:
--   Theorem 4.3(a) — worst-case shortage is regularly varying
-- statement:
--   For every $\alpha>1$, $m_1>0$, and $m_\alpha>m_1^\alpha$, the worst-case expected shortage has regular-variation index $-(\alpha-1)$:
--
--   $$\Pi_{1,\alpha}\in RV_{-(\alpha-1)}.$$
--
--   This is the first clause of Theorem 4.3 and covers $\alpha=2$ as well as both ranges of Proposition 3.4. Regular variation means that $\Pi_{1,\alpha}(tq)/\Pi_{1,\alpha}(q)\to t^{-(\alpha-1)}$ for every $t>0$, with an eventually positive denominator.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 28, Theorem 4.3(a)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

theorem theorem_4_3_a (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1)
    (hma : m1 ^ α < ma) :
    IsRegularlyVarying (worstCase m1 ma α) (-(α - 1)) := by sorry

end HeavyTailNV.Tail
