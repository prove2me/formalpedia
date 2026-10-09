-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_proposition_3_4_b
-- name    : HeavyTailNV.Tail.proposition_3_4_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:17.226005+00:00
-- url     : https://prove2.me/theorems/202c6767-97c0-4a3c-b5a3-a0c4350a947f
-- title:
--   Proposition 3.4(b) — upper bound when 1 < α < 2
-- statement:
--   Suppose $1<\alpha<2$, $m_1>0$, $m_\alpha>m_1^\alpha$, and $0<\varepsilon<(\alpha/(\alpha-1))^{\alpha-1}-\alpha$. Let $x^*$ be the unique root larger than $(\alpha+\varepsilon)^{1/(\alpha-1)}$ of
--
--   $$x^\alpha-(\alpha+\varepsilon)x+1-(x^{\alpha-1}-\alpha-\varepsilon+1)^{\alpha/(\alpha-1)}=0.$$
--
--   The proposition asserts that this unique root exists and, for every $q>m_1(\alpha-1)x^*/\alpha$,
--
--   $$\Pi_{1,\alpha}(q)\le\frac{(m_\alpha-m_1^\alpha)(\alpha-1)^{\alpha-1}}{\alpha^\alpha q^{\alpha-1}-(\alpha+\varepsilon)\alpha m_1^{\alpha-1}(\alpha-1)^{\alpha-1}}.$$
--
--   The root and strict threshold give a finite upper bound in the subquadratic moment regime.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 19, Proposition 3.4(b), (3.25)–(3.26)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

theorem proposition_3_4_b (α m1 ma ε : ℝ) (hα1 : 1 < α) (hα2 : α < 2)
    (hm1 : 0 < m1) (hma : m1 ^ α < ma) (hε0 : 0 < ε)
    (hε : ε < (α / (α - 1)) ^ (α - 1) - α) :
    (∃! x : ℝ, (α + ε) ^ (1 / (α - 1)) < x ∧ rootEq α ε x = 0) ∧
    ∀ x : ℝ, (α + ε) ^ (1 / (α - 1)) < x → rootEq α ε x = 0 →
      ∀ q : ℝ, m1 * (α - 1) * x / α < q →
        worstCase m1 ma α q ≤
          (ma - m1 ^ α) /
            (α ^ α * q ^ (α - 1) - (α + ε) * α * m1 ^ (α - 1) *
              (α - 1) ^ (α - 1)) * (α - 1) ^ (α - 1) := by sorry

end HeavyTailNV.Tail
