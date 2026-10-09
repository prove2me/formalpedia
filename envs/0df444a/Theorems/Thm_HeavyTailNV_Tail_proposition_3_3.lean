-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_proposition_3_3
-- name    : HeavyTailNV.Tail.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:08.696983+00:00
-- url     : https://prove2.me/theorems/d045b853-6051-448e-9839-04a754870d7b
-- title:
--   Proposition 3.3 — lower bound on worst-case shortage
-- statement:
--   For $\alpha>1$, $m_1>0$, and $m_\alpha>m_1^\alpha$, define the threshold $\underline q$ by (3.14). At every $q>\underline q(m_1,m_\alpha,\alpha)$,
--
--   $$\Pi_{1,\alpha}(q)\ge\frac{m_\alpha-m_1^\alpha}{\alpha^\alpha q^{\alpha-1}}(\alpha-1)^{\alpha-1}.$$
--
--   This lower bound fixes the leading constant of the power-law decay of worst-case shortage.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 15, Proposition 3.3, (3.13)–(3.14)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

theorem proposition_3_3 (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1)
    (hma : m1 ^ α < ma) :
    ∀ q : ℝ, qLower m1 ma α < q →
      (ma - m1 ^ α) / (α ^ α * q ^ (α - 1)) * (α - 1) ^ (α - 1) ≤
        worstCase m1 ma α q := by sorry

end HeavyTailNV.Tail
