-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_scarf_bound
-- name    : HeavyTailNV.Tail.scarf_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:10.983286+00:00
-- url     : https://prove2.me/theorems/3d5ced03-1d62-4b19-94c8-c8ce8a42faff
-- title:
--   (1.3) — Scarf's piecewise worst-case expected shortage
-- statement:
--   Let $m_1>0$ and $m_2>m_1^2$ be the first and second moments of nonnegative demand. Scarf's two-moment model has the piecewise worst-case shortage
--
--   $$\Pi_{1,2}(q)=\begin{cases}\frac12\bigl(\sqrt{q^2-2m_1q+m_2}-(q-m_1)\bigr),&q\ge m_2/(2m_1),\\m_1-qm_1^2/m_2,&0\le q<m_2/(2m_1).\end{cases}$$
--
--   The first branch supplies the missing $\alpha=2$ upper bound in the regular-variation argument. The two branches include the shared boundary in the first case.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 3, (1.3)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

theorem scarf_bound (m1 m2 : ℝ) (hm1 : 0 < m1)
    (hm2 : m1 ^ (2 : ℝ) < m2) :
    (∀ q : ℝ, m2 / (2 * m1) ≤ q →
      worstCase m1 m2 (2 : ℝ) q =
        (1 / 2 : ℝ) * (Real.sqrt (q ^ 2 - 2 * m1 * q + m2) - (q - m1))) ∧
    (∀ q : ℝ, 0 ≤ q → q < m2 / (2 * m1) →
      worstCase m1 m2 (2 : ℝ) q = m1 - q * m1 ^ 2 / m2) := by sorry

end HeavyTailNV.Tail
