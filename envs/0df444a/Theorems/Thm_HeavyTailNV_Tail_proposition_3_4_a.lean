-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_proposition_3_4_a
-- name    : HeavyTailNV.Tail.proposition_3_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:26:58.954972+00:00
-- url     : https://prove2.me/theorems/774fc460-7218-45e6-9239-5ba72d1fa0b2
-- title:
--   Proposition 3.4(a) — upper bound when α > 2
-- statement:
--   Suppose $\alpha>2$, $m_1>0$, and $m_\alpha>m_1^\alpha$. For every $q>\bar q(m_1,\alpha)$, where $\bar q=m_1(\alpha-1)\alpha^{(2-\alpha)/(\alpha-1)}$,
--
--   $$\Pi_{1,\alpha}(q)\le\frac{(m_\alpha-m_1^\alpha)(\alpha-1)^{\alpha-1}}{\alpha^\alpha q^{\alpha-1}-\alpha^2m_1^{\alpha-1}(\alpha-1)^{\alpha-1}}.$$
--
--   Together with Proposition 3.3, this identifies the power-law order of the worst-case shortage. The denominator is positive above the stated strict threshold.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 19, Proposition 3.4(a), (3.23)–(3.24)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

theorem proposition_3_4_a (α m1 ma : ℝ) (hα : 2 < α) (hm1 : 0 < m1)
    (hma : m1 ^ α < ma) :
    ∀ q : ℝ, qUpper m1 α < q →
      worstCase m1 ma α q ≤
        (ma - m1 ^ α) /
          (α ^ α * q ^ (α - 1) - α ^ (2 : ℝ) * m1 ^ (α - 1) *
            (α - 1) ^ (α - 1)) * (α - 1) ^ (α - 1) := by sorry

end HeavyTailNV.Tail
